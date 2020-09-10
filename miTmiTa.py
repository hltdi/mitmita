#!/usr/bin/env python3

# Mainumby: Parsing and translation with minimal dependency grammars.
#
########################################################################
#
#   This file is part of the HLTDI L^3 project
#   for parsing, generation, translation, and computer-assisted
#   human translation.
#
#   Copyleft 2014, 2015, 2016, 2017, 2018; HLTDI, PLoGS <gasser@indiana.edu>
#   
#   This program is free software: you can redistribute it and/or
#   modify it under the terms of the GNU General Public License as
#   published by the Free Software Foundation, either version 3 of
#   the License, or (at your option) any later version.
#   
#   This program is distributed in the hope that it will be useful,
#   but WITHOUT ANY WARRANTY; without even the implied warranty of
#   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
#   GNU General Public License for more details.
#   
#   You should have received a copy of the GNU General Public License
#   along with this program. If not, see <http://www.gnu.org/licenses/>.
#
# =========================================================================

# 2017.4
# -- English->Amharic
# -- Split off from mainumby as miTmiTa.py
# 2020.8
# -- Updated with changes to mainumby
# -- Amharic->Chaha

__version__ = 1.0

import iwqet

## shortcuts

FS = iwqet.morpho.FeatStruct
FSS = iwqet.morpho.FSSet

def load(train=False):
    amh, sgw = iwqet.Language.load_trans('amh', 'sgw', train=train)
    return amh, sgw

def tra(oracion, html=False, user=None, choose=False, verbosity=0):
    return ora(oracion, user=user, max_sols=2, translate=True,
               connect=True, generate=True, html=html, choose=choose,
               verbosity=verbosity)

## Creación (y opcionalmente traducción) de oración simple y de documento.

def ora(text, user=None, max_sols=2, translate=True,
        connect=True, generate=False, html=False, choose=False, verbosity=0):
    return kuaa.oración(text, user=user, max_sols=max_sols, translate=translate,
                        connect=connect, generate=generate, html=html, choose=choose,
                        verbosity=verbosity)

def anal(sentence, user=None, verbosity=0):
    """Analizar una oración castellana."""
    return kuaa.oración(sentence, user=user, translate=False, verbosity=verbosity)

def document(text, process=True):
    a = iwqet.Language.languages.get('amh')
    s = iwqet.Language.languages.get('sgw')
    if not a:
        a, s = load()
#        e = load1()
    d = iwqet.Document(a, s, text=text, proc=process)
    return d

def sent(text, user=None, max_sols=2, translate=True,
        connect=True, generate=False, html=False, choose=False, verbosity=0):
    return iwqet.አረፍተነገር(text, user=user, max_sols=max_sols, translate=translate,
                        connect=connect, generate=generate, html=html, choose=choose,
                        verbosity=verbosity)

def sentence(sentence, ambig=False, solve=True, user=None, segment=True,
             max_sols=1, verbosity=0):
    e, a = load()
    gui = iwqet.gui.GUI()
    gui.source = e
    gui.target = a
    iwqet.start(gui, user)
    d = iwqet.Document(e, a, sentence, True)
    s = d[0]
    s.initialize(ambig=ambig, verbosity=verbosity)
    if solve or segment:
        s.solve(all_sols=ambig or max_sols>1, max_sols=max_sols)
        if s.solutions and segment:
            solution = s.solutions[0]
            solution.get_segs()
        output_sols(s)
    return s

def generate(language, stem, feats=None, pos='v'):
    if not feats:
        feats = iwqet.FeatStruct("[]")
    else:
        feats = iwqet.FeatStruct(feats)
    return language.generate(stem, feats, pos)

def solve1(sentence):
    """Solve; print and return solutions."""
    sentence.solve()
    output_sols(sentence)
    return sentence.solutions

def load1(lang='eng'):
    l = iwqet.Language.load_lang(lang)
    return l

def output_sols(sentence):
    """Show target outputs for all solutions for sentence."""
    for sol in sentence.solutions:
        print(sol.get_ttrans_outputs())

def arch_doc(lengua, ruta, session=None, user=None, proc=False):
    """Crear un documento del contenido de un archivo, solo para análisis."""
    l = cargar(lengua)
    session = session or iwqet.start(l, None, user)
    arch = open(ruta, encoding='utf8')
    texto = arch.read()
    d = iwqet.Document(l, None, texto, proc=proc, session=session)
    return d

def usuario(username):
    return iwqet.User.users.get(username)

# Load a language for analysis.
def load_lang(lang='eng'):
    eng = iwqet.Language.load_lang(lang)
    return eng

if __name__ == "__main__":
    print("ወደ ሚጥሚጣ እንኳን ደህና መጡ! version {}\n".format(__version__))
