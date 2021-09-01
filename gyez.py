#!/usr/bin/env python3

# Gyez: CAT for Amharic-Guragina.
#
########################################################################
#
#   This file is part of the PLoGS project
#   for parsing, generation, translation, and computer-assisted
#   human translation.
#
#   Copyleft 2020, 2021; PLoGS <gasser@indiana.edu>
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
#
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
    return sent(oracion, user=user, max_sols=2, translate=True,
               connect=True, generate=True, html=html, choose=choose,
               verbosity=verbosity)

# test sentences, including named entities
T1 = "በቀለም ደረሰ።"
T2 = "እደብረ ብርሃን ደረስን።"
T3 = "በጊ መጣች።"
T4 = "የበጊ ቤት ነው።"

## Creation (and optionally translation) of simple sentences.

def anal(sentence, user=None, verbosity=0):
    """Analyze an Amharic sentence."""
    return iwqet.አረፍተነገር(sentence, user=user, translate=False, verbosity=verbosity)

def document(text, process=True):
    a = iwqet.Language.languages.get('amh')
    s = iwqet.Language.languages.get('sgw')
    if not a:
        a, s = load()
    d = iwqet.Document(a, s, text=text, proc=process)
    return d

def sent(text, user=None, max_sols=3, translate=True,
        connect=True, generate=False, html=False, choose=False, verbosity=0):
    return iwqet.አረፍተነገር(text, user=user, max_sols=max_sols, translate=translate,
                        connect=connect, generate=generate, html=html, choose=choose,
                        verbosity=verbosity)

def sentence(sentence, ambig=False, solve=True, user=None, segment=True,
             max_sols=1, verbosity=0):
    a, g = load()
    gui = iwqet.gui.GUI()
    gui.source = a
    gui.target = g
    iwqet.start(gui, user)
    d = iwqet.Document(a, g, sentence, True)
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

def load1(lang='amh'):
    l = iwqet.Language.load_lang(lang)
    return l

def output_sols(sentence):
    """Show target outputs for all solutions for sentence."""
    for sol in sentence.solutions:
        print(sol.get_ttrans_outputs())

def ሰነድ(ቋንቋ, ዱካ, session=None, ተጠቃሚ=None, proc=False):
    """
    Create a document from the content of a file, only for analysis.
    """
    l = load1(ቋንቋ)
    session = session or iwqet.start(l, None, ተጠቃሚ)
    arch = open(ዱካ, encoding='utf8')
    ጽሁፍ = arch.read()
    d = iwqet.Document(l, None, ጽሁፍ, proc=proc, session=session)
    return d

## Database

def db_texts():
    texts = \
          [iwqet.Text.read("ነብርናፍየል", domain="ተረቶች", title="የነብር ግልገልና የፍየል ግልገል", segment=True)]
    iwqet.db.session.add_all(texts)

def db_add_text(file='', title='', domain=''):
    text = iwqet.Text.read(file, title=title, domain=domain, segment=True)
    iwqet.db.session.add(text)

def db_users():
    db_create_admin()
    db_create_anon()
    db_create_old_users()

def db_reinit():
    iwqet.db.create_all()
    iwqet.db.session = iwqet.db.create_scoped_session()

def db_create_admin():
    admin = iwqet.Human(username='admin', email='gasser@indiana.edu',
                            name="አስተዳዳሪ", password='wsa')
    iwqet.db.session.add(admin)

def db_create_anon():
    anon = iwqet.Human(username='anon', email='onlyskybl@gmail.com',
                          name="ስምአልባ")
    iwqet.db.session.add(anon)

# Utilities

def db_get(typ):
    """
    Get all instances of DB typ (for example, iwqet.Text) in session.
    """
    return typ.query.all()

def db_delete(obj):
    """
    Delete the object from the session.
    """
    iwqet.db.session.delete(obj)

def db_commit():
    """
    Commit all changes during this session.
    """
    iwqet.db.session.commit()

if __name__ == "__main__":
    print("ወደ ጘዝ እንኳን ደህና መጡ! version {}\n".format(__version__))
