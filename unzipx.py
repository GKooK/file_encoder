#!/usr/bin/env python3
"""unzipx - zipx 로 만든 압축 파일을 푸는 전용 프로그램.

이 파일 하나만 있으면 압축을 풀 수 있다. 파이썬 표준 라이브러리 외에는
아무것도 필요하지 않으며, 압축(만들기) 기능은 들어 있지 않다.
압축 파일을 받는 사람에게 이 파일만 같이 건네주면 된다.

    ./unzipx.py 자료.zipx                # 현재 폴더에 풀기
    ./unzipx.py 자료.zipx -d 풀어낼폴더
    ./unzipx.py 자료.zipx -l             # 풀지 않고 목록만 보기
    ./unzipx.py 자료.zipx -t             # 무결성 검사만

압축 파일 구조 (zipx 와 동일):

    scrypt(비밀번호, salt) → 키 64B ┬→ 앞 32B: AES-256-CTR 복호화 키
                                    └→ 뒤 32B: HMAC-SHA256 인증 키

    매직(8) │ KDF파라미터(4) │ salt(16) │ IV(16) │ 헤더태그(16) │ 암호문 … │ HMAC-SHA256(32)
"""
from __future__ import annotations

import argparse
import getpass
import hashlib
import hmac
import os
import struct
import sys
import time
import zipfile
from pathlib import Path

__version__ = "2.0.0"

# ============================================================ 1. AES-256
# 표준 라이브러리에는 AES 가 없어 직접 구현한다.
# pycryptodome / cryptography 가 이미 설치되어 있으면 그쪽 C 구현을 자동으로
# 빌려 써서 빨라진다. 없어도 아래 순수 파이썬 구현으로 그대로 동작한다.


def _build_tables():
    """AES S-box 와 라운드 변환용 T-table 을 생성한다."""
    p = q = 1
    sbox = [0] * 256
    while True:
        p ^= ((p << 1) & 0xFF) ^ (0x1B if p & 0x80 else 0)
        q ^= (q << 1) & 0xFF
        q ^= (q << 2) & 0xFF
        q ^= (q << 4) & 0xFF
        if q & 0x80:
            q ^= 0x09
        value = q ^ ((q << 1) | (q >> 7)) ^ ((q << 2) | (q >> 6)) \
            ^ ((q << 3) | (q >> 5)) ^ ((q << 4) | (q >> 4))
        sbox[p] = (value ^ 0x63) & 0xFF
        if p == 1:
            break
    sbox[0] = 0x63
    t0 = []
    for s in sbox:
        s2 = ((s << 1) ^ 0x1B) & 0xFF if s & 0x80 else s << 1
        t0.append((s2 << 24) | (s << 16) | (s << 8) | (s2 ^ s))
    t1 = [((v >> 8) | (v << 24)) & 0xFFFFFFFF for v in t0]
    t2 = [((v >> 8) | (v << 24)) & 0xFFFFFFFF for v in t1]
    t3 = [((v >> 8) | (v << 24)) & 0xFFFFFFFF for v in t2]
    return bytes(sbox), t0, t1, t2, t3


_SBOX, _T0, _T1, _T2, _T3 = _build_tables()
_RCON = (0x01000000, 0x02000000, 0x04000000, 0x08000000,
         0x10000000, 0x20000000, 0x40000000)


class PureAES256:
    """순수 파이썬 AES-256 (CTR 모드라 복호화도 암호화 방향으로 처리한다)."""

    __slots__ = ("_rk",)
    ROUNDS = 14

    def __init__(self, key: bytes):
        if len(key) != 32:
            raise ValueError("AES-256 키는 32바이트여야 합니다.")
        rk = list(struct.unpack(">8I", key))
        for i in range(8, 4 * (self.ROUNDS + 1)):
            word = rk[i - 1]
            if i % 8 == 0:
                word = ((word << 8) | (word >> 24)) & 0xFFFFFFFF
                word = self._sub(word) ^ _RCON[i // 8 - 1]
            elif i % 8 == 4:
                word = self._sub(word)
            rk.append(rk[i - 8] ^ word)
        self._rk = rk

    @staticmethod
    def _sub(word: int) -> int:
        s = _SBOX
        return ((s[(word >> 24) & 0xFF] << 24) | (s[(word >> 16) & 0xFF] << 16)
                | (s[(word >> 8) & 0xFF] << 8) | s[word & 0xFF])

    def encrypt(self, data: bytes) -> bytes:
        """16바이트 배수 길이의 데이터를 ECB 로 암호화한다."""
        rk, sbox = self._rk, _SBOX
        t0, t1, t2, t3 = _T0, _T1, _T2, _T3
        out = bytearray(len(data))
        for off in range(0, len(data), 16):
            s0, s1, s2, s3 = struct.unpack_from(">4I", data, off)
            s0 ^= rk[0]; s1 ^= rk[1]; s2 ^= rk[2]; s3 ^= rk[3]
            k = 4
            for _ in range(self.ROUNDS - 1):
                s0, s1, s2, s3 = (
                    t0[s0 >> 24] ^ t1[(s1 >> 16) & 0xFF] ^ t2[(s2 >> 8) & 0xFF] ^ t3[s3 & 0xFF] ^ rk[k],
                    t0[s1 >> 24] ^ t1[(s2 >> 16) & 0xFF] ^ t2[(s3 >> 8) & 0xFF] ^ t3[s0 & 0xFF] ^ rk[k + 1],
                    t0[s2 >> 24] ^ t1[(s3 >> 16) & 0xFF] ^ t2[(s0 >> 8) & 0xFF] ^ t3[s1 & 0xFF] ^ rk[k + 2],
                    t0[s3 >> 24] ^ t1[(s0 >> 16) & 0xFF] ^ t2[(s1 >> 8) & 0xFF] ^ t3[s2 & 0xFF] ^ rk[k + 3])
                k += 4
            struct.pack_into(">4I", out, off,
                             self._final(sbox, s0, s1, s2, s3) ^ rk[k],
                             self._final(sbox, s1, s2, s3, s0) ^ rk[k + 1],
                             self._final(sbox, s2, s3, s0, s1) ^ rk[k + 2],
                             self._final(sbox, s3, s0, s1, s2) ^ rk[k + 3])
        return bytes(out)

    @staticmethod
    def _final(s, a, b, c, d) -> int:
        return ((s[a >> 24] << 24) | (s[(b >> 16) & 0xFF] << 16)
                | (s[(c >> 8) & 0xFF] << 8) | s[d & 0xFF])


def _pick_aes():
    """설치되어 있으면 C 구현을, 없으면 순수 파이썬 구현을 쓴다."""
    for name in ("Crypto.Cipher.AES", "Cryptodome.Cipher.AES"):
        try:
            aes = __import__(name, fromlist=["AES"])
        except ImportError:
            continue
        return name.split(".")[0], lambda key, a=aes: a.new(key, a.MODE_ECB)
    try:
        from cryptography.hazmat.primitives.ciphers import Cipher, algorithms, modes

        class _ECB:
            def __init__(self, key):
                self._c = Cipher(algorithms.AES(key), modes.ECB())

            def encrypt(self, data):
                enc = self._c.encryptor()
                return enc.update(data) + enc.finalize()

        return "cryptography", _ECB
    except ImportError:
        return "순수 파이썬", PureAES256


AES_BACKEND, new_aes = _pick_aes()


# ============================================================ 2. CTR 스트림

class CTRStream:
    """AES-256-CTR 로 감싼 읽기 전용 파일 객체.

    임의 위치 읽기를 지원하므로 표준 zipfile 이 이 위에서 그대로 동작한다.
    논리 위치 0 이 실제 파일의 start 위치에 해당한다.
    """

    _MASK = (1 << 128) - 1

    def __init__(self, fp, key: bytes, iv: bytes, start: int, size: int):
        self._fp, self._cipher = fp, new_aes(key)
        self._iv = int.from_bytes(iv, "big")
        self._start, self._size = start, size
        self._pos = 0

    def _crypt(self, data: bytes, offset: int) -> bytes:
        first, skip = offset // 16, offset % 16
        nblocks = (skip + len(data) + 15) // 16
        keystream = bytearray()
        while nblocks:
            take = min(nblocks, 4096)
            keystream += self._cipher.encrypt(b"".join(
                ((self._iv + first + i) & self._MASK).to_bytes(16, "big")
                for i in range(take)))
            first += take
            nblocks -= take
        keystream = bytes(keystream[skip:skip + len(data)])
        # 바이트 단위 반복보다 큰 정수 XOR 이 훨씬 빠르다.
        return (int.from_bytes(data, "big")
                ^ int.from_bytes(keystream, "big")).to_bytes(len(data), "big")

    def readable(self):
        return True

    def writable(self):
        return False

    def seekable(self):
        return True

    def tell(self):
        return self._pos

    def seek(self, offset, whence=0):
        self._pos = (0, self._pos, self._size)[whence] + offset
        if self._pos < 0:
            raise ValueError("음수 위치로는 이동할 수 없습니다.")
        return self._pos

    def read(self, size=-1):
        if size is None or size < 0:
            size = max(0, self._size - self._pos)
        else:
            size = min(size, max(0, self._size - self._pos))
        if not size:
            return b""
        self._fp.seek(self._start + self._pos)
        data = self._crypt(self._fp.read(size), self._pos)
        self._pos += len(data)
        return data


# ============================================================ 3. 컨테이너

MAGIC = b"ZIPXBOX1"
HEADER_LEN = 60      # 매직8 + 파라미터4 + salt16 + IV16 + 헤더태그16
TAG_LEN = 32
CHUNK = 1 << 20


class ZipxError(Exception):
    """일반 오류."""


class WrongPassword(ZipxError):
    """비밀번호가 틀림."""


class Tampered(ZipxError):
    """내용이 위·변조되었거나 손상됨."""


def _derive(password: str, salt: bytes, logn: int, r: int, p: int):
    """비밀번호에서 (복호화 키 32B, 인증 키 32B) 를 유도한다."""
    if not hasattr(hashlib, "scrypt"):
        raise ZipxError("이 파이썬은 scrypt 를 지원하지 않습니다 (OpenSSL 1.1 이상 필요).")
    n = 1 << logn
    need = 128 * n * r
    material = hashlib.scrypt(password.encode("utf-8"), salt=salt, n=n, r=r, p=p,
                              dklen=64, maxmem=need * 2 + (1 << 21))
    return material[:32], material[32:]


class BoxReader:
    """컨테이너를 연다. .stream 으로 안쪽 ZIP 을 읽는다."""

    def __init__(self, path, password: str):
        self.path = Path(path)
        self._fp = open(self.path, "rb")
        try:
            head = self._fp.read(HEADER_LEN)
            if len(head) < HEADER_LEN or head[:8] != MAGIC:
                raise ZipxError("zipx 로 만든 압축 파일이 아닙니다.")
            logn, r, p, _ = head[8:12]
            salt, iv, head_tag = head[12:28], head[28:44], head[44:60]
            total = self.path.stat().st_size
            if total < HEADER_LEN + TAG_LEN:
                raise Tampered("파일이 잘려 있습니다.")
            self.kdf = f"scrypt N=2^{logn} r={r} p={p} ({(128 << logn) * r / 2**20:.0f} MiB)"
            self.size = total - HEADER_LEN - TAG_LEN
            enc_key, self._mac_key = _derive(password, salt, logn, r, p)
            # 헤더 태그만으로 비밀번호를 즉시 판별한다 (전체를 읽을 필요가 없다).
            if not hmac.compare_digest(
                    hmac.new(self._mac_key, head[:44], hashlib.sha256).digest()[:16], head_tag):
                raise WrongPassword("비밀번호가 올바르지 않습니다.")
            self.stream = CTRStream(self._fp, enc_key, iv, HEADER_LEN, self.size)
        except BaseException:
            self._fp.close()
            raise

    def authenticate(self):
        """암호문 전체의 인증 태그를 확인한다 (복호화 전에 호출)."""
        self._fp.seek(0)
        mac = hmac.new(self._mac_key, digestmod=hashlib.sha256)
        remaining = HEADER_LEN + self.size
        while remaining > 0:
            block = self._fp.read(min(CHUNK, remaining))
            if not block:
                raise Tampered("파일이 잘려 있습니다.")
            mac.update(block)
            remaining -= len(block)
        if not hmac.compare_digest(mac.digest(), self._fp.read(TAG_LEN)):
            raise Tampered("무결성 검사 실패: 위·변조되었거나 손상된 파일입니다.")
        self.stream.seek(0)

    def __enter__(self):
        return self

    def __exit__(self, *_):
        self._fp.close()
        return False


# ============================================================ 4. 해제

def _safe_target(dest: Path, name: str) -> Path:
    """Zip Slip 방지: 결과 경로가 반드시 대상 폴더 안에 있도록 만든다."""
    parts = [x for x in name.replace("\\", "/").split("/") if x not in ("", ".", "..")]
    if not parts:
        raise ZipxError(f"잘못된 항목 이름입니다: {name!r}")
    root = dest.resolve()
    target = (root / Path(*parts)).resolve()
    if target != root and root not in target.parents:
        raise ZipxError(f"압축 파일 밖으로 벗어나는 경로입니다: {name!r}")
    return target


def _open(archive, password: str, authenticate=False):
    """컨테이너를 열어 (BoxReader, ZipFile) 를 돌려준다."""
    archive = Path(archive).expanduser()
    if not archive.is_file():
        raise ZipxError(f"압축 파일을 찾을 수 없습니다: {archive}")
    box = BoxReader(archive, password)
    try:
        if authenticate:
            box.authenticate()
        return box, zipfile.ZipFile(box.stream)
    except BaseException:
        box.__exit__()
        raise


def listing(archive, password: str) -> list:
    """압축 파일 안의 항목 목록. 목록 자체가 암호문 안에 있어 비밀번호가 필요하다."""
    box, zf = _open(archive, password)
    with box, zf:
        return zf.infolist()


def extract(archive, dest, password: str, progress=None) -> dict:
    """압축을 해제한다. 인증 태그를 먼저 확인한 뒤에만 파일을 쓴다."""
    dest = Path(dest).expanduser()
    box, zf = _open(archive, password, authenticate=True)
    written = 0
    with box, zf:
        infos = zf.infolist()
        total = sum(i.file_size for i in infos)
        done = 0
        dest.mkdir(parents=True, exist_ok=True)
        for info in infos:
            target = _safe_target(dest, info.filename)
            if info.is_dir():
                target.mkdir(parents=True, exist_ok=True)
                continue
            if progress:
                progress(done, total, info.filename)
            target.parent.mkdir(parents=True, exist_ok=True)
            try:
                with zf.open(info) as src, open(target, "wb") as out:
                    while True:
                        block = src.read(CHUNK)
                        if not block:
                            break
                        out.write(block)
                        done += len(block)
                        if progress:
                            progress(done, total, info.filename)
            except BaseException:
                target.unlink(missing_ok=True)
                raise
            try:
                stamp = time.mktime(tuple(info.date_time) + (0, 0, -1))
                os.utime(target, (stamp, stamp))
            except (ValueError, OverflowError, OSError):
                pass
            written += 1
    return {"files": written, "dest": dest.resolve()}


def test(archive, password: str, progress=None) -> dict:
    """전체를 읽어 인증 태그와 각 항목의 CRC 를 검사한다."""
    box, zf = _open(archive, password, authenticate=True)
    with box, zf:
        infos = [i for i in zf.infolist() if not i.is_dir()]
        total = sum(i.file_size for i in infos)
        done = 0
        broken = []
        for info in infos:
            if progress:
                progress(done, total, info.filename)
            try:
                with zf.open(info) as fp:
                    while True:
                        block = fp.read(CHUNK)
                        if not block:
                            break
                        done += len(block)
                        if progress:
                            progress(done, total, info.filename)
            except (zipfile.BadZipFile, OSError):
                broken.append(info.filename)
        return {"checked": len(infos), "broken": broken}


# ============================================================ 5. 명령줄

def human(n: float) -> str:
    for unit in ("B", "KB", "MB", "GB", "TB"):
        if n < 1024 or unit == "TB":
            return f"{n:,.0f} {unit}" if unit == "B" else f"{n:,.1f} {unit}"
        n /= 1024


class Bar:
    """터미널용 진행률 표시 (파이프로 연결되면 자동으로 조용해진다)."""

    def __init__(self, label, quiet=False):
        self.label = label
        self.on = not quiet and sys.stderr.isatty()
        self.started = self._last = time.time()

    def __call__(self, done, total, name):
        now = time.time()
        if not self.on or (now - self._last < 0.05 and done != total):
            return
        self._last = now
        ratio = min(max(done / total if total else 1.0, 0.0), 1.0)
        filled = int(28 * ratio)
        shown = name if len(name) <= 30 else "…" + name[-29:]
        sys.stderr.write(f"\r  {self.label} [{'█' * filled}{'░' * (28 - filled)}]"
                         f" {ratio * 100:5.1f}%  {shown:<30.30s}")
        sys.stderr.flush()

    def clear(self):
        if self.on:
            sys.stderr.write("\r" + " " * 78 + "\r")
            sys.stderr.flush()

    @property
    def elapsed(self):
        return time.time() - self.started


def get_password(given) -> str:
    if given:
        return given
    if not sys.stdin.isatty():
        raise ZipxError("대화형 터미널이 아닙니다. -p 뒤에 비밀번호를 직접 지정하세요.")
    while True:
        password = getpass.getpass("비밀번호: ")
        if password:
            return password
        print("빈 비밀번호는 쓸 수 없습니다.", file=sys.stderr)


def show_list(archive, password) -> int:
    infos = listing(archive, password)
    files = [i for i in infos if not i.is_dir()]
    print(f"{Path(archive).resolve()}  "
          f"({human(Path(archive).stat().st_size)}, 🔐 암호화됨)")
    print(f"{'크기':>12}  {'압축크기':>12}  {'날짜':<16}  이름")
    print("-" * 74)
    for info in infos:
        stamp = "%04d-%02d-%02d %02d:%02d" % info.date_time[:5]
        size = "<폴더>" if info.is_dir() else f"{info.file_size:,}"
        packed = "" if info.is_dir() else f"{info.compress_size:,}"
        print(f"{size:>12}  {packed:>12}  {stamp:<16}  {info.filename}")
    print("-" * 74)
    print(f"파일 {len(files)}개 · 원본 {human(sum(i.file_size for i in files))}")
    return 0


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(
        prog="unzipx", formatter_class=argparse.RawDescriptionHelpFormatter,
        description="zipx 로 만든 압축 파일을 푸는 전용 프로그램 (표준 라이브러리만 사용)",
        epilog="""사용 예:
  unzipx.py 자료.zipx                 # 현재 폴더에 풀기
  unzipx.py 자료.zipx -d 풀어낼폴더
  unzipx.py 자료.zipx -l              # 풀지 않고 목록만 보기
  unzipx.py 자료.zipx -t              # 무결성 검사만
""")
    parser.add_argument("archive", help="풀어낼 압축 파일")
    parser.add_argument("-d", "--dest", default=".", help="풀어낼 폴더 (기본: 현재 폴더)")
    parser.add_argument("-p", "--password", default=None, metavar="비밀번호",
                        help="비밀번호. 생략하면 화면에 보이지 않게 입력받는다.")
    parser.add_argument("-l", "--list", action="store_true",
                        help="풀지 않고 목록만 보여준다.")
    parser.add_argument("-t", "--test", action="store_true",
                        help="풀지 않고 무결성만 검사한다.")
    parser.add_argument("-q", "--quiet", action="store_true", help="진행 표시 끄기")
    parser.add_argument("-V", "--version", action="version",
                        version=f"unzipx {__version__} (AES 백엔드: {AES_BACKEND})")
    args = parser.parse_args(argv)

    try:
        password = get_password(args.password)
        if args.list:
            return show_list(args.archive, password)
        if args.test:
            bar = Bar("검사 중", args.quiet)
            result = test(args.archive, password, progress=bar)
            bar.clear()
            if result["broken"]:
                print(f"손상된 항목 {len(result['broken'])}개:")
                for name in result["broken"]:
                    print(f"  - {name}")
                return 1
            print(f"이상 없음: {result['checked']}개 항목 검사 완료 ({bar.elapsed:.1f}초)")
            return 0
        bar = Bar("해제 중", args.quiet)
        result = extract(args.archive, args.dest, password, progress=bar)
        bar.clear()
        if not args.quiet:
            print(f"해제 완료: {result['dest']}")
            print(f"  파일 {result['files']}개 · {bar.elapsed:.1f}초")
        return 0
    except ZipxError as exc:
        print(f"오류: {exc}", file=sys.stderr)
        return 2
    except KeyboardInterrupt:
        print("\n중단되었습니다.", file=sys.stderr)
        return 130


if __name__ == "__main__":
    sys.exit(main())
