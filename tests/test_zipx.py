"""zipx 테스트 (표준 라이브러리만 사용).

실행:  python3 -m unittest discover -s tests -v
"""
import hashlib
import io
import os
import shutil
import subprocess
import sys
import tempfile
import unittest
import zipfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))

import zipx
from zipx import Tampered, WrongPassword, ZipxError

PASSWORD = "테스트 비밀번호 Aa1!"
KDF = "normal"          # 테스트 속도를 위해 낮은 강도


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def tree(root):
    """폴더 안의 파일 해시와 빈 폴더 목록."""
    root = Path(root)
    out = {}
    for path in sorted(root.rglob("*")):
        rel = path.relative_to(root).as_posix()
        if path.is_file():
            out[rel] = digest(path)
        elif path.is_dir() and not any(path.iterdir()):
            out[rel + "/"] = "DIR"
    return out


class Base(unittest.TestCase):
    def setUp(self):
        self.tmp = Path(tempfile.mkdtemp(prefix="zipx-test-"))
        self.src = self.tmp / "자료"
        (self.src / "문서" / "하위").mkdir(parents=True)
        (self.src / "빈폴더").mkdir()
        (self.src / "문서" / "한글 이름.txt").write_text("가나다라마바사\n" * 300,
                                                    encoding="utf-8")
        (self.src / "문서" / "하위" / "random.bin").write_bytes(os.urandom(250_000))
        (self.src / "big.bin").write_bytes(os.urandom(3_000_000))   # 청크 경계 확인
        (self.src / "empty.txt").write_text("")
        (self.src / "ascii.txt").write_text("hello world\n" * 50)
        self.expected = tree(self.src)

    def tearDown(self):
        shutil.rmtree(self.tmp, ignore_errors=True)

    def make(self, name="a.zipx", sources=None, password=PASSWORD, **kwargs):
        archive = self.tmp / name
        kwargs.setdefault("kdf", KDF)
        kwargs.setdefault("overwrite", True)
        zipx.create(archive, sources or [self.src], password, **kwargs)
        return archive


class TestRoundTrip(Base):
    def test_roundtrip(self):
        archive = self.make()
        out = self.tmp / "out"
        result = zipx.extract(archive, out, PASSWORD)
        self.assertEqual(tree(out / "자료"), self.expected)
        self.assertEqual(result["files"], 5)

    def test_single_file(self):
        archive = self.make("one.zipx", [self.src / "ascii.txt"])
        out = self.tmp / "one"
        zipx.extract(archive, out, PASSWORD)
        self.assertEqual(digest(out / "ascii.txt"), digest(self.src / "ascii.txt"))

    def test_multiple_sources(self):
        archive = self.make("multi.zipx", [self.src / "ascii.txt", self.src / "문서"])
        out = self.tmp / "multi"
        zipx.extract(archive, out, PASSWORD)
        self.assertTrue((out / "ascii.txt").exists())
        self.assertEqual(tree(out / "문서"), tree(self.src / "문서"))

    def test_all_kdf_levels(self):
        for level in ("normal", "high"):
            with self.subTest(kdf=level):
                archive = self.make(f"{level}.zipx", [self.src / "ascii.txt"], kdf=level)
                out = self.tmp / f"o_{level}"
                zipx.extract(archive, out, PASSWORD)
                self.assertEqual(digest(out / "ascii.txt"), digest(self.src / "ascii.txt"))

    def test_compression_levels(self):
        for level in (0, 1, 9):
            with self.subTest(level=level):
                archive = self.make(f"l{level}.zipx", [self.src / "문서"], level=level)
                out = self.tmp / f"ol{level}"
                zipx.extract(archive, out, PASSWORD)
                self.assertEqual(tree(out / "문서"), tree(self.src / "문서"))

    def test_empty_dir_preserved(self):
        archive = self.make()
        out = self.tmp / "out"
        zipx.extract(archive, out, PASSWORD)
        self.assertTrue((out / "자료" / "빈폴더").is_dir())

    def test_listing(self):
        archive = self.make()
        names = [i.filename for i in zipx.listing(archive, PASSWORD)]
        self.assertIn("자료/ascii.txt", names)
        self.assertIn("자료/문서/한글 이름.txt", names)

    def test_test_command(self):
        archive = self.make(sources=[self.src / "문서"])
        self.assertEqual(zipx.test(archive, PASSWORD)["broken"], [])


class TestSecurity(Base):
    def test_wrong_password(self):
        archive = self.make()
        with self.assertRaises(WrongPassword):
            zipx.extract(archive, self.tmp / "no", "틀린암호")
        self.assertFalse((self.tmp / "no").exists())
        with self.assertRaises(WrongPassword):
            zipx.listing(archive, "틀린암호")

    def test_filenames_hidden(self):
        """평문 파일 이름이나 ZIP 흔적이 남아 있으면 안 된다."""
        archive = self.make()
        blob = archive.read_bytes()
        for needle in (b"ascii.txt", b"big.bin", b"random.bin", b"PK\x03\x04",
                       "한글 이름.txt".encode("utf-8")):
            self.assertNotIn(needle, blob, f"{needle!r} 이(가) 노출됨")

    def test_not_readable_as_zip(self):
        archive = self.make(sources=[self.src / "ascii.txt"])
        with self.assertRaises(zipfile.BadZipFile):
            zipfile.ZipFile(archive)

    def test_tamper_detected(self):
        archive = self.make(sources=[self.src / "문서"])
        size = archive.stat().st_size
        for position in (zipx.HEADER_LEN + 5, size // 2, size - zipx.TAG_LEN - 1,
                         size - 1):
            with self.subTest(position=position):
                raw = bytearray(archive.read_bytes())
                raw[position] ^= 0x01
                target = self.tmp / "bad.zipx"
                target.write_bytes(bytes(raw))
                with self.assertRaises(Tampered):
                    zipx.extract(target, self.tmp / "bad_out", PASSWORD)

    def test_header_tamper_detected(self):
        """헤더를 건드리면 비밀번호가 맞아도 거부되어야 한다."""
        archive = self.make(sources=[self.src / "ascii.txt"])
        raw = bytearray(archive.read_bytes())
        raw[30] ^= 0x01                      # IV 훼손
        target = self.tmp / "h.zipx"
        target.write_bytes(bytes(raw))
        with self.assertRaises(WrongPassword):
            zipx.extract(target, self.tmp / "h_out", PASSWORD)

    def test_truncation_detected(self):
        archive = self.make(sources=[self.src / "문서"])
        target = self.tmp / "cut.zipx"
        target.write_bytes(archive.read_bytes()[:-40])
        with self.assertRaises(Tampered):
            zipx.extract(target, self.tmp / "cut_out", PASSWORD)

    def test_not_our_format(self):
        other = self.tmp / "plain.zip"
        with zipfile.ZipFile(other, "w") as zf:
            zf.writestr("a.txt", "x")
        with self.assertRaises(ZipxError):
            zipx.listing(other, PASSWORD)

    def test_every_archive_differs(self):
        """같은 내용·같은 비밀번호라도 salt/IV 가 매번 달라 결과가 달라야 한다."""
        first = self.make("s1.zipx", [self.src / "ascii.txt"])
        second = self.make("s2.zipx", [self.src / "ascii.txt"])
        self.assertNotEqual(first.read_bytes(), second.read_bytes())
        self.assertNotEqual(first.read_bytes()[12:44], second.read_bytes()[12:44])

    def test_file_permissions(self):
        archive = self.make(sources=[self.src / "ascii.txt"])
        self.assertEqual(archive.stat().st_mode & 0o777, 0o600)

    def test_zip_slip_blocked(self):
        """대상 폴더 밖으로 나가는 경로는 안쪽으로 정규화된다."""
        target = self.tmp / "evil.zipx"
        with zipx.BoxWriter(target, PASSWORD, KDF) as box:
            with zipfile.ZipFile(box.stream, "w") as zf:
                zf.writestr("../../pwned.txt", "x")
        dest = self.tmp / "dest"
        zipx.extract(target, dest, PASSWORD)
        self.assertTrue((dest / "pwned.txt").exists())
        self.assertFalse((self.tmp / "pwned.txt").exists())

    def test_password_required(self):
        with self.assertRaises(ZipxError):
            zipx.create(self.tmp / "np.zipx", [self.src / "ascii.txt"], "")

    def test_no_overwrite_by_default(self):
        archive = self.make(sources=[self.src / "ascii.txt"])
        with self.assertRaises(ZipxError):
            zipx.create(archive, [self.src / "ascii.txt"], PASSWORD, kdf=KDF)

    def test_failed_create_leaves_nothing(self):
        archive = self.tmp / "fail.zipx"
        with self.assertRaises(ZipxError):
            zipx.create(archive, [self.src / "없는파일.txt"], PASSWORD, kdf=KDF)
        self.assertFalse(archive.exists())
        self.assertFalse(archive.with_name(archive.name + ".part").exists())


class TestCrypto(unittest.TestCase):
    def test_aes256_fips197_vector(self):
        plain = bytes.fromhex("00112233445566778899aabbccddeeff")
        self.assertEqual(zipx.PureAES256(bytes(range(32))).encrypt(plain).hex(),
                         "8ea2b7ca516745bfeafc49904b496089")

    def test_backend_matches_pure_python(self):
        key, data = os.urandom(32), os.urandom(4096)
        self.assertEqual(zipx.new_aes(key).encrypt(data),
                         zipx.PureAES256(key).encrypt(data))

    def test_ctr_random_access(self):
        key, iv, data = os.urandom(32), os.urandom(16), os.urandom(10_000)
        buf = io.BytesIO()
        writer = zipx.CTRStream(buf, key, iv, 0, size=0, writable=True)
        writer.write(data[:3000])
        writer.write(data[3000:])          # 이어 쓰기
        patch = ("덮어쓴 내용" * 10).encode("utf-8")
        writer.seek(1234)
        writer.write(patch)                # 중간으로 되돌아가 덮어쓰기
        expected = bytearray(data)
        expected[1234:1234 + len(patch)] = patch

        reader = zipx.CTRStream(io.BytesIO(buf.getvalue()), key, iv, 0, size=len(data))
        self.assertEqual(reader.read(), bytes(expected))
        reader.seek(5000)
        self.assertEqual(reader.read(100), bytes(expected[5000:5100]))
        reader.seek(-10, 2)
        self.assertEqual(reader.read(), bytes(expected[-10:]))

    def test_ctr_chunk_alignment(self):
        """조각내어 쓴 결과와 한 번에 쓴 결과가 같아야 한다."""
        key, iv, data = os.urandom(32), os.urandom(16), os.urandom(5000)
        one = io.BytesIO()
        zipx.CTRStream(one, key, iv, 0, size=0, writable=True).write(data)
        many = io.BytesIO()
        stream = zipx.CTRStream(many, key, iv, 0, size=0, writable=True)
        pos = 0
        for n in (1, 15, 16, 17, 100, 999, 3, 4849):
            stream.write(data[pos:pos + n])
            pos += n
        self.assertEqual(one.getvalue(), many.getvalue())

    def test_derive_is_deterministic(self):
        salt = os.urandom(16)
        self.assertEqual(zipx._derive("암호", salt, 14, 8, 1),
                         zipx._derive("암호", salt, 14, 8, 1))
        self.assertNotEqual(zipx._derive("암호", salt, 14, 8, 1),
                            zipx._derive("암호2", salt, 14, 8, 1))


class TestCLI(Base):
    def run_cli(self, *args):
        return subprocess.run([sys.executable, str(ROOT / "zipx.py"), *args],
                              capture_output=True, text=True)

    def test_cli_roundtrip(self):
        archive = self.tmp / "cli.zipx"
        result = self.run_cli("c", str(archive), str(self.src / "문서"),
                              "-p", PASSWORD, "--kdf", KDF, "-o", "-q")
        self.assertEqual(result.returncode, 0, result.stderr)

        result = self.run_cli("l", str(archive), "-p", PASSWORD)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("한글 이름.txt", result.stdout)

        out = self.tmp / "cliout"
        result = self.run_cli("x", str(archive), "-d", str(out), "-p", PASSWORD, "-q")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(tree(out / "문서"), tree(self.src / "문서"))

        result = self.run_cli("t", str(archive), "-p", PASSWORD, "-q")
        self.assertEqual(result.returncode, 0, result.stderr)

    def test_cli_wrong_password(self):
        archive = self.tmp / "cli2.zipx"
        self.run_cli("c", str(archive), str(self.src / "ascii.txt"),
                     "-p", PASSWORD, "--kdf", KDF, "-o", "-q")
        result = self.run_cli("x", str(archive), "-d", str(self.tmp / "x"),
                              "-p", "틀림", "-q")
        self.assertEqual(result.returncode, 2)
        self.assertIn("비밀번호", result.stderr)
        self.assertFalse((self.tmp / "x").exists())


class TestUnzipx(Base):
    """해제 전용 프로그램(unzipx.py)이 zipx 로 만든 파일을 그대로 풀어야 한다."""

    def run_unzipx(self, *args, script=None):
        return subprocess.run([sys.executable, str(script or ROOT / "unzipx.py"), *args],
                              capture_output=True, text=True)

    def test_extracts_zipx_archive(self):
        archive = self.make()
        out = self.tmp / "out"
        result = self.run_unzipx(str(archive), "-d", str(out), "-p", PASSWORD, "-q")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(tree(out / "자료"), self.expected)

    def test_standalone(self):
        """다른 폴더에 이 파일만 복사해도 동작해야 한다 (zipx.py 없이)."""
        alone = self.tmp / "배포" / "unzipx.py"
        alone.parent.mkdir()
        shutil.copy(ROOT / "unzipx.py", alone)
        self.assertFalse((alone.parent / "zipx.py").exists())
        archive = self.make(sources=[self.src / "문서"])
        out = self.tmp / "alone_out"
        result = self.run_unzipx(str(archive), "-d", str(out), "-p", PASSWORD, "-q",
                                 script=alone)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(tree(out / "문서"), tree(self.src / "문서"))

    def test_list_and_test_options(self):
        archive = self.make(sources=[self.src / "문서"])
        result = self.run_unzipx(str(archive), "-l", "-p", PASSWORD)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("한글 이름.txt", result.stdout)
        self.assertFalse((self.tmp / "문서" / "한글 이름.txt").exists())  # 풀지 않았음

        result = self.run_unzipx(str(archive), "-t", "-p", PASSWORD, "-q")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("이상 없음", result.stdout)

    def test_wrong_password(self):
        archive = self.make(sources=[self.src / "ascii.txt"])
        out = self.tmp / "no"
        result = self.run_unzipx(str(archive), "-d", str(out), "-p", "틀림", "-q")
        self.assertEqual(result.returncode, 2)
        self.assertIn("비밀번호", result.stderr)
        self.assertFalse(out.exists())

    def test_tamper_rejected(self):
        archive = self.make(sources=[self.src / "문서"])
        raw = bytearray(archive.read_bytes())
        raw[len(raw) // 2] ^= 0x01
        bad = self.tmp / "bad.zipx"
        bad.write_bytes(bytes(raw))
        result = self.run_unzipx(str(bad), "-d", str(self.tmp / "bad_out"),
                                 "-p", PASSWORD, "-q")
        self.assertEqual(result.returncode, 2)
        self.assertIn("무결성", result.stderr)

    def test_rejects_other_files(self):
        other = self.tmp / "plain.zip"
        with zipfile.ZipFile(other, "w") as zf:
            zf.writestr("a.txt", "x")
        result = self.run_unzipx(str(other), "-p", PASSWORD, "-q")
        self.assertEqual(result.returncode, 2)

    def test_has_no_compression_code(self):
        """해제 전용이므로 압축 기능이 들어 있으면 안 된다."""
        sys.path.insert(0, str(ROOT))
        import unzipx
        self.assertFalse(hasattr(unzipx, "create"))
        self.assertFalse(hasattr(unzipx, "BoxWriter"))

    def test_same_container_constants(self):
        """두 프로그램의 컨테이너 형식이 어긋나면 안 된다."""
        import unzipx
        self.assertEqual(unzipx.MAGIC, zipx.MAGIC)
        self.assertEqual(unzipx.HEADER_LEN, zipx.HEADER_LEN)
        self.assertEqual(unzipx.TAG_LEN, zipx.TAG_LEN)
        key = os.urandom(32)
        data = os.urandom(1024)
        self.assertEqual(unzipx.PureAES256(key).encrypt(data),
                         zipx.PureAES256(key).encrypt(data))


if __name__ == "__main__":
    unittest.main(verbosity=2)
