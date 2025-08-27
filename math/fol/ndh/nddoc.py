#!/usr/bin/env python3

# A tool that documents all definitions, axioms and proven theorems

from sys import argv
from os.path import isdir
from os import mkdir

DIR_NAME = "proofs-doc"

class Env:
    def __init__(self):
        self.toc = []
        self.section_count = 0
        self.chapter_count = 0
        self.def_count = 0
        self.axiom_count = 0
        self.thm_count = 0
        self.buf = []
        self.proofs = []
        self.dependencies = set()
        self.dep_db = {}
        self.propose_clear = False
        self.title = None
        self.rules = set()

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
    while i < len(s) and not s[i].isspace():
        i += 1
    cmd = s[:i].lower()
    content = s[i+1:].strip()
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
    elif cmd == "title":
        env.title = content
    elif cmd == "rules":
        for rule in content.split():
            env.rules.add(rule)

def consume_ident_list(s, n, i):
    idents = []
    while i < n:
        if s[i] in ".,": break
        i, ident = consume_ident(s, n, i)
        idents.append(ident)
        i = consume_space(s, n, i)
    return i, idents

non_link = {"axiom", "def"}

def link_ident(ident):
    if ident[0].isalpha() and not ident in non_link:
        return f"<a href='{ident}.htm'>{ident}</a>"
    else:
        return ident

def update_dependencies(env, idents):
    for ident in idents:
        if ident[0].isalpha():
            env.dependencies.add(ident)

def extract(s, acc, env):
    i = 0; n = len(s)
    while i < n:
        if s[i].isspace():
            i += 1
        elif s[i] == '#':
            i += 1
            while i < n and s[i] != '\n': i += 1
            i += 1
        elif s[i] == '(' and i + 1 < n and s[i + 1] == '*':
            i += 2; j = i
            cmd = i < n and s[i] == '/'
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
            if ident.isdigit() and int(ident) > 1:
                env.propose_clear = False
            i = consume_space(s, n, i)
            while i < n and not s[i] in "|(⊢":
                i += 1
            i0 = i
            if s[i] == "⊢": i0 += 1
            elif i + 1 < n and s[1] == "|" and s[i+1] == "-": i0 += 2
            if i0 < n and s[i0] == ' ': i0 += 1
            j = consume_until(',', s, n, i)
            i = consume_space(s, n, j + 1)
            if i + 2 < n and s[i:i+3] == "def":
                kind = "Definition"; cl = "def"
            elif i + 4 < n and s[i:i+5] == "axiom":
                kind = "Axiom"; cl = "ax"
            elif i + 3 < n and s[i:i+4] == "rule":
                kind = "Rule"; cl = "rule"
            else:
                kind = "Theorem"; cl = "thm"
            if named and ident in env.rules:
                kind = "Rule"; cl = "rule"
            idents_from = i
            i, idents = consume_ident_list(s, n, i)
            idents_to = i
            i = consume_until('.', s, n, i) + 1
            if env.propose_clear:
                env.dependencies.clear()
                env.buf.clear()
                env.propose_clear = False
            update_dependencies(env, idents)
            idents = " ".join(link_ident(x) for x in idents)
            env.buf.append(s[start:idents_from] + idents + s[idents_to:i])
            if named:
                acc.append(f"<div class='box'><div class='{cl}'><b class='{cl}'>{kind}.</b> ")
                acc.append(f"<a href='{DIR_NAME}/{ident}.htm'>{ident}</a><br>\n{s[i0:j]}</div></div>\n")
                item = (f"<div class='box'><div class='{cl}'><b class='{cl}'>{kind}.</b> "
                  + f"{ident}<br>\n{s[i0:j]}</div></div>\n")
                env.proofs.append({
                    "ident": ident, "kind": kind, "item": item,
                    "proof": "\n".join(env.buf)
                })
                env.dep_db[ident] =  (kind, env.dependencies.copy())
                env.propose_clear = True
                if kind == "Definition":
                    env.def_count += 1
                elif kind == "Axiom":
                    env.axiom_count += 1
                elif kind == "Theorem":
                    env.thm_count += 1

CSS_FONTS = """\
"DejaVu Sans Mono", "Menlo", "Consolas", monospace\
"""

CSS_COMMON = """\
pre{font-size: 12pt;}
a{color: #00304a; text-decoration: none;}
a:hover{color: #d00090; text-decoration: underline;}
div.box{
  border-top: 2px solid #cacac2;
  border-bottom: 2px solid #cacac2;
  margin-top: 0.5em;
  margin-bottom: 0.5em;
}
div.def, div.thm, div.ax, div.rule{
  padding-left: 12px;
  padding-right: 12px;
  padding-top: 4px;
  padding-bottom: 4px;
  background-color: #fafaf0;
}
div.def {border-left: 6px solid #006000;}
div.thm {border-left: 6px solid #000080;}
div.ax  {border-left: 6px solid #d0a000;}
div.rule{border-left: 6px solid #900060;}
b.def {color: #006000;}
b.thm {color: #000080;}
b.ax  {color: #d0a000;}
b.rule{color: #900060;}\
"""

def header(acc):
    acc.append(f"""\
<!DOCTYPE html>
<html>
<head>
  <meta charset="UTF-8">
  <title>Library</title>
  <style>
body{{
  font-family: {CSS_FONTS};
  font-size: 12pt;
  margin-left: 6%;
  margin-right: 6%;
  line-height: 1.5;
  margin-top: 2em;
  margin-bottom: 6em;
}}
{CSS_COMMON}
  </style>
</head>
<body>
""")

main_css = f"""
body{{
  font-family: {CSS_FONTS};
  font-size: 12pt;
  margin-left: 10%;
  margin-right: 10%;
  line-height: 1.5;
  margin-top: 4em;
  margin-bottom: 6em;
}}
{CSS_COMMON}
"""

def footer(acc):
    acc.append("\n</body>\n</html>")

def sublist(a):
    if len(a) == 0: return ""
    acc = ["<ol>\n"]
    for x in a:
        acc.append(f"<li><a href='#{x[1]}'>{x[0]}</a>{sublist(x[2])}\n")
    acc.append("</ol>")
    return "".join(acc)
        

def table_of_contents(toc):
    return f"<h2>Table of contents</h2>\n{sublist(toc)}\n"

def depends_on_axioms(acc, ident, dep_db):
    kind, dependencies = dep_db[ident]
    if kind != "Theorem": return acc
    for x in dependencies:
        if x in dep_db:
            kind = dep_db[x][0]
            if kind == "Axiom": acc.add(x)
            depends_on_axioms(acc, x, dep_db)
    return acc

def number_as_word(n):
    return (
        "one" if n == 1 else
        "two" if n == 2 else
        "three" if n == 3 else
        "four" if n == 4 else
        "five" if n == 5 else
        "six" if n == 6 else
        "seven" if n == 7 else
        "eight" if n == 8 else
        "nine" if n == 9 else
        str(n))

def proof_file(env, kwargs):
    ident = kwargs["ident"]
    kind = kwargs["kind"]
    item = kwargs["item"]
    text = kwargs["proof"]
    if kind == "Theorem":
        text = f"<pre><b>Proof</b>\n{text}\n</pre>"
    else:
        text = ""
    axiom_deps = sorted(depends_on_axioms(set(), ident, env.dep_db))
    if len(axiom_deps) != 0:
        n = len(axiom_deps)
        axiom_deps = [f"<a href='{x}.htm'>{x}</a>" for x in axiom_deps]
        axiom_deps = ', '.join(axiom_deps)
        axiom_count = "one axiom" if n == 1 else f"{number_as_word(n)} axioms"
        axiom_deps = ("\n<p><b>Dependencies</b><br>" +
            f"The given proof depends on {axiom_count}:<br>{axiom_deps}.</p>")
    else:
        axiom_deps = ""
    return f"""\
<!DOCTYPE html>
<html>
<head>
  <meta charset="UTF-8">
  <title>{ident}</title>
  <link href="main.css" rel="stylesheet">
</head>
<body>
<h3>{kind} {ident}</h3>
{item}{text}{axiom_deps}
</body>
</html>\
"""

def main():
    env = Env()
    acc = []; count = 0
    header(acc)
    title_pos = len(acc)
    acc.append("")
    toc_pos = len(acc)
    acc.append("")
    for name in argv[1:]:
        with open(name, "r") as fin:
            s = fin.read()
            extract(s, acc, env)
    acc.append("<p><b>Statistics</b>\n<pre>\n")
    acc.append(f"{env.def_count:4} definitions\n")
    acc.append(f"{env.axiom_count:4} axioms\n")
    acc.append(f"{env.thm_count:4} theorems\n")
    total_count = env.def_count + env.axiom_count + env.thm_count
    acc.append("────────────────\n")
    acc.append(f"{total_count:4} items total\n</pre>")
    footer(acc)
    if len(env.toc) != 0:
        acc[toc_pos] = table_of_contents(env.toc)
    if not env.title is None:
        acc[title_pos] = f"<h1>{env.title}</h1>\n"
    with open("proofs-doc.htm", "w") as fout:
        fout.write("".join(acc))
    if not isdir(f"./{DIR_NAME}"):
        mkdir(f"./{DIR_NAME}")
    for proof in env.proofs:
        ident = proof["ident"]
        with open(f"{DIR_NAME}/{ident}.htm", "w") as fout:
            fout.write(proof_file(env, proof))
    with open(f"{DIR_NAME}/main.css", "w") as fout:
        fout.write(main_css)

main()
