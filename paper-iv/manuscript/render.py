"""Build from editable Markdown with Pandoc, Chromium and Python Playwright."""
from pathlib import Path
import subprocess, os, shutil, sys, tempfile
from playwright.sync_api import sync_playwright
r=Path(__file__).resolve().parent
subprocess.run([sys.executable, str(r.parent / "verify_claims.py"), "--check"], check=True)
style="""
@page{size:letter;margin:0}
*{box-sizing:border-box} body{margin:0;color:#193345;font:11.0pt/1.43 "DejaVu Serif",serif;background:#fff}
.sheet{position:relative;width:8.5in;height:11in;padding:.73in .72in .65in;break-after:page;border-top:6px solid #106d63;background:#fff}
.sheet:last-child{break-after:auto}.sheet header,.sheet footer{position:absolute;left:.72in;right:.72in;display:flex;justify-content:space-between;color:#50716f;font:600 8pt "DejaVu Sans",sans-serif;letter-spacing:.065em;}
.sheet header{top:.30in}.sheet footer{bottom:.27in;border-top:1px solid #c5d8d2;padding-top:7px;font-weight:400}
h1,h2,h3{break-after:avoid}h1{font:700 23pt/1.12 "DejaVu Serif",serif;letter-spacing:-.025em;margin:0 0 .24in;color:#17384a}
.p1 h1{font-size:28pt;margin-bottom:.13in}h2{font:700 13pt/1.2 "DejaVu Sans",sans-serif;color:#136b60;margin:.22in 0 .10in}
.subtitle{font:400 15pt/1.27 "DejaVu Sans",sans-serif;color:#146b63}.byline{font:9pt/1.35 "DejaVu Sans",sans-serif;color:#516970;margin:.18in 0 .23in}
p{margin:.092in 0}.callout{font:10.2pt/1.45 "DejaVu Sans",sans-serif;background:#e9f3ee;border-left:4px solid #18806c;padding:.13in .16in;margin:.15in 0}
table{width:100%;border-collapse:collapse;margin:.11in 0;font:9.3pt/1.35 "DejaVu Sans",sans-serif}
th{background:#176a60;color:#fff;text-align:left;padding:7px 8px}td{border-bottom:1px solid #d0ded8;padding:6px 8px}tbody tr:nth-child(even){background:#f1f6f3}
.math{font-family:"Latin Modern Math","DejaVu Math TeX Gyre",serif}math[display=block]{font-size:1.03em;margin:.11in 0}math{font-family:"Latin Modern Math","DejaVu Math TeX Gyre",serif}
figure{margin:0;text-align:center}figure figcaption{display:none}img.wide{width:100%;max-height:3.3in;object-fit:contain}img.joint{width:78%;max-height:2.88in;object-fit:contain}
img.acoustic{width:100%;max-height:3.20in;object-fit:contain}.p9 table{font-size:8.6pt}.p10 table{font-size:9pt;line-height:1.3}.p10 th,.p10 td{padding:5px 6px}.p9 th,.p9 td{padding:5px 6px}
img{max-width:100%}p:has(>em:only-child){font:9.2pt/1.37 "DejaVu Sans",sans-serif;color:#52676d}
strong{color:#163647}th strong{color:#fff}li{margin:.03in 0}
a{color:#116b63;text-decoration:underline}ol{padding-left:.24in}
section.references ol{font:9.2pt/1.38 "DejaVu Sans",sans-serif}
.smallnote{border-top:1px solid #ccdbd4;padding-top:.075in;font:8.7pt/1.35 "DejaVu Sans",sans-serif;color:#546873;margin-top:.11in}
.proofphoto{width:97%;height:6.7in;object-fit:contain}.widehold{width:100%;max-height:4.15in;object-fit:contain}.milestone{width:6.94in;height:auto}
"""
title = 'Sharp space–time covariance bounds for the Riemann Xi profile'
section_name = 'MANUSCRIPT  /  REVISION 4'
src = (r/'manuscript.md').read_text().split('<!--page-->')
pages=[]
for i,s in enumerate(src,1):
 content=subprocess.run(['pandoc','-f','markdown+raw_html+tex_math_dollars','-t','html5','--mathml','--wrap=none'],input=s,text=True,capture_output=True,check=True).stdout
 extra=' references' if s.lstrip().startswith('# References') else ''
 pages.append(f'<section class="sheet p{i}{extra}"><header><span>GENESIS  /  MATHEMATICAL RESEARCH</span><span>{section_name}</span></header><main>{content}</main><footer><span>{title.upper()}</span><span>{i:02}</span></footer></section>')
# A local intermediate lets Chromium resolve figures relative to this source.
with tempfile.NamedTemporaryFile(dir=r, suffix='.html', delete=False) as html_file:
    out = Path(html_file.name)
out.write_text('<meta charset="utf-8"><title>'+title+'</title><style>'+style+'</style>'+''.join(pages))
pdf_path = r.parent / 'Paper-IV.pdf'
with sync_playwright() as p:
    b=p.chromium.launch(headless=True,executable_path=os.environ.get('CHROME_PATH') or shutil.which('chromium'),args=['--no-sandbox','--allow-file-access-from-files'])
    page=b.new_page();page.goto(out.as_uri(),wait_until='load');page.emulate_media(media='print')
    page.evaluate("document.fonts.ready")
    sizes=page.locator('.sheet').evaluate_all("""items=>items.map(x=>[x.className,Math.round(x.querySelector('footer').getBoundingClientRect().top-x.querySelector('main').getBoundingClientRect().bottom)])""")
    print('Vertical space before footer, CSS pixels:',sizes)
    assert min(v for _,v in sizes)>=12
    assert page.locator('math').count()>5
    assert page.locator('img').evaluate_all("imgs=>imgs.every(x=>x.complete&&x.naturalWidth>0)")
    page.pdf(path=str(pdf_path),print_background=True,prefer_css_page_size=True,tagged=True)
    b.close()
import fitz
import re
out.unlink()
with fitz.open(pdf_path) as d:
    assert len(d)==len(pages)
    d.set_toc([[1,re.search(r'^# (.+)$',section,re.M).group(1),i] for i,section in enumerate(src,1)]+[])
    metadata=d.metadata
    metadata.update(title=title,subject=section_name+', 27 November 2026',author='Ian Walker')
    from pdf_provenance import source_fingerprint
    metadata['keywords'] = 'paper-iv-source-sha256=' + source_fingerprint()
    d.set_metadata(metadata)
    d.save(str(r/'bookmarked.pdf'),garbage=4,deflate=True)
(r/'bookmarked.pdf').replace(pdf_path)
