#!/usr/bin/env python3
"""Build the Morse Theory exposition: PDF (pandoc + XeLaTeX) and web edition (HTML + MathJax).

Usage: python3 build.py [targets...]   targets: 1..15, A, or names like Chapter3; default all.
       python3 build.py --figs         regenerate every static figure first.
"""
import glob, os, re, subprocess, sys

import checked_marks

HERE = os.path.dirname(os.path.abspath(__file__))
WEB = os.path.join(HERE, "web")

PDF_ARGS = [
    "--pdf-engine=xelatex",
    "-V", "mainfont=Palatino", "-V", "mathfont=latinmodern-math.otf",
    "-V", "geometry:margin=1in", "-V", "papersize=letter", "-V", "fontsize=11pt",
    "-V", "colorlinks=true", "-V", "linkcolor=blue", "-V", "urlcolor=blue",
    "-V", "header-includes=\\usepackage{amssymb}\\usepackage{float}\\floatplacement{figure}{H}",
    "--resource-path", HERE,
]

WEB_HEAD = """<!doctype html><html lang="en"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>{title}</title>
<script>window.MathJax={{svg:{{fontCache:'global'}}}};</script>  <!-- defaults read pandoc's \\( \\) and \\[ \\] -->
<script src="https://cdnjs.cloudflare.com/ajax/libs/mathjax/3.2.2/es5/tex-svg.js"></script>
<style>
:root{{--fg:#1d1d1f;--bg:#fbfaf7;--accent:#b4441f;--muted:#8a8780;--rule:#e2dfd8}}
@media (prefers-color-scheme: dark){{:root:not([data-theme="light"]){{--fg:#e8e6e1;--bg:#1b1a18;--accent:#f08a5d;--muted:#9c978d;--rule:#38352f}}}}
:root[data-theme="dark"]{{--fg:#e8e6e1;--bg:#1b1a18;--accent:#f08a5d;--muted:#9c978d;--rule:#38352f}}
body{{background:var(--bg);color:var(--fg);font:17px/1.6 "Iowan Old Style",Palatino,Georgia,serif;margin:0;padding:0 16px}}
main{{max-width:46rem;margin:2.5rem auto 5rem}}
h1{{font-size:1.9rem;line-height:1.25}} h2{{margin-top:2.4rem;border-top:1px solid var(--rule);padding-top:1.2rem}}
blockquote{{border-left:3px solid var(--accent);margin:1rem 0;padding:.2rem 1rem;color:var(--fg);background:color-mix(in srgb,var(--accent) 6%,transparent)}}
table{{border-collapse:collapse;display:block;overflow-x:auto;font-size:.92rem}} td,th{{border:1px solid var(--rule);padding:.35rem .55rem;vertical-align:top}}
mjx-container[display="true"]{{overflow-x:auto;overflow-y:hidden}}
code{{font-size:.9em}} a{{color:var(--accent)}} hr{{border:0;border-top:1px solid var(--rule)}}
[id$="-figure"]{{margin:1.5rem 0}}
.checked{{font-size:.86em;color:var(--muted)}}
mjx-container.wide{{display:inline-block;max-width:100%;overflow-x:auto;overflow-y:hidden;vertical-align:middle}}
</style></head><body><main>
"""

def targets(argv):
    names = []
    for a in argv:
        if a.upper() == "A":
            names.append("Appendix")
        elif a.isdigit():
            names.append(f"Chapter{a}")
        else:
            names.append(a)
    if not names:
        names = [f"Chapter{i}" for i in range(1, 16)] + ["Appendix"]
    return [n for n in names if os.path.exists(os.path.join(HERE, n + ".md"))]

def figures_of(md):
    return re.findall(r"!\[[^\]]*\]\((fig[^)]+\.png)\)", md)

def build_pdf(name, md):
    out = os.path.join(HERE, name + ".pdf")
    r = subprocess.run(["pandoc", "-f", "markdown-implicit_figures", "-o", out] + PDF_ARGS,
                       input=re.sub(r'<div id="[^"]+"></div>\n?', "", md),
                       text=True, capture_output=True, cwd=HERE)
    if r.returncode:
        print(f"[{name}] PDF FAILED\n{r.stderr[-3000:]}")
        return False
    print(f"[{name}] PDF ok -> {os.path.basename(out)}")
    return True

def build_web(name, md):
    os.makedirs(WEB, exist_ok=True)
    web_md = re.sub(r"\*\(In the printed version[^)]*\)\*\s*\n", "", md)
    web_md = re.sub(r"!\[[^\]]*\]\(fig[^)]+\.png\)\s*\n", "", web_md)
    r = subprocess.run(["pandoc", "-f", "markdown", "-t", "html5", "--mathjax"],
                       input=web_md, text=True, capture_output=True)
    if r.returncode:
        print(f"[{name}] WEB FAILED\n{r.stderr}")
        return
    scripts = ""
    for png in figures_of(md):
        js = os.path.join(HERE, png[:-4] + ".js")
        if os.path.exists(js):
            scripts += "<script>\n" + open(js).read() + "\n</script>\n"
    title = re.search(r"^# (.+)$", md, re.M)
    title = title.group(1) if title else name
    fit = ("<script>(function(){var m=document.querySelector('main');if(!m||!window.MutationObserver)return;"
           "function f(c){if(!c||c.getAttribute('display')==='true'||!c.parentElement)return;"
           "if(c.getBoundingClientRect().width>c.parentElement.getBoundingClientRect().width+1)c.classList.add('wide');}"
           "new MutationObserver(function(rs){rs.forEach(function(r){var t=r.target.nodeType===1?r.target:r.target.parentElement;"
           "var c=t&&t.closest?t.closest('mjx-container'):null;if(c)f(c);});}).observe(m,{childList:true,subtree:true});})();</script>\n")
    html = WEB_HEAD.format(title=title.replace('"', "")) + r.stdout + "</main>\n" + scripts + fit + "</body></html>\n"
    open(os.path.join(WEB, name + ".html"), "w").write(html)
    print(f"[{name}] web ok -> web/{name}.html")

def main():
    argv = sys.argv[1:]
    if "--figs" in argv:
        argv.remove("--figs")
        for py in sorted(glob.glob(os.path.join(HERE, "fig*.py"))):
            subprocess.run([sys.executable, py], cwd=HERE, check=False)
    for name in targets(argv):
        md = open(os.path.join(HERE, name + ".md")).read()
        for png in figures_of(md):
            if not os.path.exists(os.path.join(HERE, png)):
                py = os.path.join(HERE, png[:-4] + ".py")
                if os.path.exists(py):
                    subprocess.run([sys.executable, py], cwd=HERE, check=False)
        md = checked_marks.mark(name, md)  # what the machine checked, at each numbered result
        build_pdf(name, md)
        build_web(name, md)

if __name__ == "__main__":
    main()
