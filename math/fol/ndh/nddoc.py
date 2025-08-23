#!/usr/bin/env python3

# A tool that documents all definitions, axioms and proven theorems

from sys import argv
from os.path import isdir
from os import mkdir

def consume_ident(s, n, i):
    j = i
    while i < n and (s[i].isalpha() or s[i].isdigit() or s[i] in "_'"):
        i += 1
    return i, s[j:i]

def consume_space(s, n, i):
    while i < n and s[i].isspace():
        i += 1
    return i

def consume_until(c, s, n, i):
    bracket_level = 0
    while i < n:
        if s[i] == c and bracket_level == 0:
            break
        elif s[i] in "{(": bracket_level += 1
        elif s[i] in "})": bracket_level -= 1
        i += 1
    return i

def id_from_text(text):
    pass

def process_command(s, acc, env):
    i = 0
    while i < len(s) and s[i] != '|':
        i += 1
    cmd = s[:i].strip().lower()
    content = s[i+2:].strip()
    if cmd == "chapter":
        env.chapter_count += 1
        env.section_count = 0
        id = str(env.chapter_count)
        acc.append(f"<h2 id='{id}'>{content}</h2>\n")
        env.toc.append((content, id, []))
    elif cmd == "section":
        env.section_count += 1
        id = f"{env.chapter_count}.{env.section_count}"
        acc.append(f"<h3 id='{id}'>{content}</h3>\n")
        env.toc[-1][2].append((content, id, []))

def consume_ident_list(s, n, i):
    idents = []
    while i < n:
        if s[i] in ".,": break
        i, ident = consume_ident(s, n, i)
        idents.append(ident)
        i = consume_space(s, n, i)
    return i, idents

non_link = {
    "axiom", "def", "wk",
    "hypo", "neg_intro", "neg_elim", "conj_intro", "conj_eliml", "conj_elimr",
    "disj_introl", "disj_intror", "disj_elim", "subj_intro", "subj_elim",
    "bij_intro", "bij_eliml", "bij_elimr", "uq_intro", "uq_elim",
    "ex_intro", "ex_elim"
}

def link_ident(ident):
    if ident[0].isalpha() and not ident in non_link:
        return f"<a href='{ident}.htm'>{ident}</a>"
    else:
        return ident

def extract(s, acc, env):
    i = 0; n = len(s)
    count = 0
    while i < n:
        if s[i].isspace():
            i += 1
        elif s[i] == '#':
            i += 1
            while i < n and s[i] != '\n': i += 1
            i += 1
        elif s[i] == '(' and i + 1 < n and s[i + 1] == '*':
            i += 2; j = i
            cmd = i < n and s[i] == '|'
            while i < n:
                if s[i] == '*' and i + 1 < n and s[i + 1] == ')':
                    if cmd: process_command(s[j+1:i], acc, env)
                    i += 2
                    break
                i += 1
        else:
            start = i
            named = i < n and (s[i+1].isalpha() or s[i+1] == '_')
            i, ident = consume_ident(s, n, i)
            i = consume_space(s, n, i)
            while i < n and not s[i] in "|(⊢":
                i += 1
            i0 = i
            if s[i] == "⊢": i0 += 1
            elif i + 1 < n and s[1] == "|" and s[i+1] == "-": i0 += 2 
            j = consume_until(',', s, n, i)
            i = consume_space(s, n, j + 1)
            if i + 2 < n and s[i:i+3] == "def":
                kind = "Definition"; cl = "def"
            elif i + 4 < n and s[i:i+5] == "axiom":
                kind = "Axiom"; cl = "ax"
            else:
                kind = "Theorem"; cl = "thm"
            idents_from = i
            i, idents = consume_ident_list(s, n, i)
            idents_to = i
            i = consume_until('.', s, n, i) + 1
            idents = " ".join(link_ident(x) for x in idents)
            env.buf.append(s[start:idents_from] + idents + s[idents_to:i])
            if named:
                acc.append(f"<div class='box'><div class='{cl}'><b class='{cl}'>{kind}.</b> ")
                acc.append(f"<a href='doc/{ident}.htm'>{ident}</a><br>{s[i0:j]}</div></div>\n")
                item = (f"<div class='box'><div class='{cl}'><b class='{cl}'>{kind}.</b> "
                  + f"{ident}<br>{s[i0:j]}</div></div>\n")
                env.proofs.append((ident, kind, item, "\n".join(env.buf)))
                env.buf.clear()
                count += 1
    return count

def header(acc):
    acc.append("""\
<!DOCTYPE html>
<html>
<head>
<meta charset="UTF-8">
<title>Library</title>
<style>
body{
  font-family: "DejaVu Sans Mono", "Menlo", "Consolas", monospace;
  margin-left: 6%;
  margin-right: 6%;
  line-height: 1.5;
  margin-top: 2em;
  margin-bottom: 6em;
}
a{color: #00304a; text-decoration: none;}
a:hover{color: #d00090; text-decoration: underline;}
table.bt{border-spacing: 0 1em;}
div.box{
  border-top: 2px solid #cacac2;
  border-bottom: 2px solid #cacac2;
  margin-top: 0.5em;
  margin-bottom: 0.5em;
}
div.def, div.thm, div.ax{
  padding-left: 12px;
  padding-right: 12px;
  padding-top: 4px;
  padding-bottom: 4px;
  background-color: #fafaf0;
}
div.def{border-left: 6px solid #006000;}
div.thm{border-left: 6px solid #000080;}
div.ax {border-left: 6px solid #d0a000;}
b.def{color: #006000;}
b.thm{color: #000080;}
b.ax {color: #d0a000;}
</style>
</head>
<body>
""")

def footer(acc):
    acc.append("<body>\n</html>")

def sublist(a):
    if len(a) == 0: return ""
    acc = ["<ol>\n"]
    for x in a:
        acc.append(f"<li><a href='#{x[1]}'>{x[0]}</a>{sublist(x[2])}\n")
    acc.append("</ol>")
    return "".join(acc)
        

def table_of_contents(toc):
    return f"<h2>Table of contents</h2>\n{sublist(toc)}\n"

class Env:
    pass

def proof_file(ident, kind, item, text):
    if kind == "Theorem":
        text = f"<br><p><b>Proof</b>\n<pre>\n{text}\n</pre>"
    else:
        text = ""
    return f"""\
<!DOCTYPE html>
<html lang="de">
<head>
  <meta charset="UTF-8">
  <title>{ident}</title>
  <link href="main.css" rel="stylesheet">
</head>
<body>
<h3>{kind} {ident}</h3>
{item}
{text}
</body>
"""

main_css = """
body{
  font-family: "DejaVu Sans Mono", "Menlo", "Consolas", monospace;
  margin-left: 10%;
  margin-right: 10%;
  line-height: 1.5;
  margin-top: 4em;
  margin-bottom: 6em;
}
pre{font-size: 12pt;}
a{color: #00304a; text-decoration: none;}
a:hover{color: #d00090; text-decoration: underline;}
table.bt{border-spacing: 0 1em;}
div.box{
  border-top: 2px solid #cacac2;
  border-bottom: 2px solid #cacac2;
  margin-top: 0.5em;
  margin-bottom: 0.5em;
}
div.def, div.thm, div.ax{
  padding-left: 12px;
  padding-right: 12px;
  padding-top: 4px;
  padding-bottom: 4px;
  background-color: #fafaf0;
}
div.def{border-left: 6px solid #006000;}
div.thm{border-left: 6px solid #000080;}
div.ax {border-left: 6px solid #d0a000;}
b.def{color: #006000;}
b.thm{color: #000080;}
b.ax {color: #d0a000;}
"""

def main():
    acc = []; count = 0
    header(acc)
    toc_pos = len(acc)
    acc.append("")
    env = Env()
    env.toc = []
    env.section_count = 0
    env.chapter_count = 0
    env.buf = []
    env.proofs = []
    for name in argv[1:]:
        with open(name, "r") as fin:
            s = fin.read()
            count += extract(s, acc, env)
    acc.append(f"<p><b>Statistics</b><br>{count} items\n")
    footer(acc)
    if len(env.toc) != 0:
        acc[toc_pos] = table_of_contents(env.toc)
    with open("doc.htm", "w") as fout:
        fout.write("".join(acc))
    if not isdir("./doc"):
        mkdir("./doc")
    for proof in env.proofs:
        with open(f"doc/{proof[0]}.htm", "w") as fout:
            fout.write(proof_file(*proof))
    with open("doc/main.css", "w") as fout:
        fout.write(main_css)

main()
