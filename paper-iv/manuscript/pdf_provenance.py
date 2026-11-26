"""Check that the committed PDF was built from this manuscript, renderer and figures."""
from hashlib import sha256
from pathlib import Path

SOURCE = Path(__file__).resolve().parent


def source_fingerprint():
    inputs = [SOURCE / "manuscript.md", SOURCE / "render.py", *sorted(SOURCE.glob("*.png"))]
    digest = sha256()
    for path in inputs:
        digest.update(path.name.encode() + b"\0" + sha256(path.read_bytes()).digest())
    return digest.hexdigest()


if __name__ == "__main__":
    import pymupdf

    manuscript = (SOURCE / "manuscript.md").read_text(encoding="utf-8")
    page_count = 1 + manuscript.count("<!--page-->")
    with pymupdf.open(SOURCE.parent / "Paper-IV.pdf") as pdf:
        if pdf.metadata.get("keywords") != "paper-iv-source-sha256=" + source_fingerprint():
            raise SystemExit("Stale PDF: rebuild with python manuscript/render.py.")
        if len(pdf) != page_count or len(pdf.get_toc()) != page_count:
            raise SystemExit("The PDF page or bookmark count differs from the manuscript.")
    print(f"PDF source, figures, {page_count} pages and bookmarks agree.")
