# Mit'mit'a. Parsing and translation with minimal dependency grammars.
#
########################################################################
#
#   This file is part of the Mit'mit'a project within the PLoGS metaproject
#   for parsing, generation, translation, and computer-assisted
#   human translation.
#
#   Copyleft 2015, 2016, 2017, 2020, 2021 HLTDI, PLoGS <gasser@indiana.edu>
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

__all__ = ['language', 'entry', 'constraint', 'views', 'variable', \
           'sentence', 'cs', 'utils', 'record', 'train', 'tag', 'gui', \
           'text', 'database', 'token']
#  not needed for now: 'learn'

from flask import Flask, url_for, render_template
from flask_sqlalchemy import SQLAlchemy

## train imports sentence
from .train import *

## sentence imports ui, segment, record
### segment imports cs, utils, entry.Entry, entry.Group, record.SegRecord
### ui imports language (ui not needed for current version)
#### language imports entry, some functions from utils, morphology.morpho, morphology.semiring
#### language also calls function in morphology.strip
##### entry imports morphology.fs

#from .sentence import *
#from .learn import *

#SESSIONS_DIR = os.path.join(os.path.dirname(__file__), 'sessions')

## morphology a package; imports morphology.morpho
### which imports morphology.fst
#### which imports morphology.semiring
##### which imports morphology.fs, morphology.utils
###### fs imports morphology.logic, morphology.internals
# from . import db

## Instantiate the Flask class to get the application
app = Flask(__name__)
app.config['SQLALCHEMY_DATABASE_URI'] = 'sqlite:///text.db'
app.config['SQLALCHEMY_BINDS'] = {
    'lex':    'sqlite:///lex.db',
    'text':   'sqlite:///text.db'
}
app.config['SQLALCHEMY_TRACK_MODIFICATIONS'] = False
db = SQLAlchemy(app)

from .morphology import *
from .record import *
from .text import *

db.create_all()

from .database import *
#app.config.from_object(__name__)

def start(gui, use_anon=True, create_memory=False):
    """
    Initiate. Create a session if there's a user.
    """
    if not gui.source:
        load(gui=gui)
    # set GUI.user
    if isinstance(gui.user, str):
        # Get the user from their username
        gui.user = get_human(gui.user)
#        User.users.get(user)
    if use_anon and not gui.user:
        gui.user = get_human('anon')
#        User.get_anon()
    username = ''
    if gui.user:
        username = gui.user.username
    if create_memory:
        gui.session = iwqet.Memory.recreate(user=username)
    elif gui.user:
        gui.session = iwqet.Session(source=gui.source, target=gui.target, user=gui.user)

def load(source='amh', target='sgw', gui=None):
    """
    Load source and target languages for translation.
    """
    s, t = iwqet.Language.load_trans(source, target)
    if gui:
        gui.source = s
        gui.target = t

def doc_sentences(doc=None, textobj=None, text='', textid=-1,
                  gui=None, src=None, targ=None, user=None, verbosity=0):
    """
    Collect sentences (instances of Sentence) from an instance
    of Document or Text.
    """
    if not src and not targ:
        if gui:
            src = gui.source; targ = gui.target
        else:
            src, targ = Language.load_trans('spa', 'grn', bidir=False)
    if doc:
        return doc
    else:
        return sentences_from_text(textobj, textid, src, targ)

def doc_trans(doc=None, textobj=None, text='', textid=-1, docpath='',
              gui=None, src=None, targ=None, session=None, user=None,
              terse=True):
    """
    Translate all the sentences in a document without offering
    options to the user.
    doc is either an instance of Document or textobj is an instance
    of Text or a Document is created with text as content.
    """
    if not src and not targ:
        if gui:
            src = gui.source; targ = gui.target
        else:
            src, targ = Language.load_trans('spa', 'grn', bidir=False)
    if not session:
        session = make_session(src, targ, user, create_memory=True)
    if not doc:
        if docpath:
            doc = Document(src, targ, path=docpath)
    if doc:
        sentences = doc
    elif textid >= 0:
        sentences = sentences_from_text(textobj, textid, src, targ)
    elif text:
        sentences = Document(src, targ, text=text)
#    sentences = doc if doc else sentences_from_text(textobj, textid, src, targ)
    if sentences:
#        print("Traduciendo oraciones en documento...")
        translations = []
#        doc = make_document(gui, text, html=False)
        for sentence in sentences:
            translation = አረፍተነገር(src=src, targ=targ, sentence=sentence, session=session,
                                  html=False, choose=True, return_string=True,
                                  verbosity=0, terse=terse)
            translations.append(translation)
#        print("  traducciones {}".format(translations[:2]))
        return translations
#        return [s.final for s in seg_sentences]
    return []

## Creación y traducción de oración, dentro o fuera de la aplicación web

def gui_trans(gui, session=None, choose=False, return_string=False,
              sentence=None, terse=True, verbosity=0):
    """
    Translate sentence (accessible in gui) and return the marked-up
    sentence (HTML) with colored segments.
    """
    return አረፍተነገር(sentence=sentence or gui.sentence, src=gui.source,
                   targ=gui.target, session=gui.session,
                   html=True, return_string=return_string, choose=choose,
                   verbosity=verbosity, terse=terse)

def አረፍተነገር(text='', src=None, targ=None, user=None, session=None,
            sentence=None,
            max_sols=2, translate=True, connect=True, generate=True,
            html=False, choose=False,
            return_string=False, verbosity=0, terse=False):
    """
    Analyze and possibly also translate a sentence from Amharic to Chaha.
    """
    if not src and not targ:
#        src = iwqet.Language.languages.get('amh')
#        targ = iwqet.Language.languages.get('sgw')
#        if not src:
        src, targ = Language.load_trans('amh', 'sgw', bidir=False)
    if not session:
        session = make_session(src, targ, user, create_memory=True)
    s = Sentence.solve_sentence(src, targ, text=text, session=session,
                                sentence=sentence,
                                max_sols=max_sols, choose=choose,
                                translate=translate,
                                verbosity=verbosity, terse=terse)
    segmentations = s.get_all_segmentations(translate=translate,
                                            generate=generate,
                                            agree_dflt=False, choose=choose,
                                            connect=connect, html=html,
                                            terse=terse)
    print("SEGMENTATIONS: {}".format(segmentations))
    if choose:
        if segmentations:
            # there's already only one of these anyway
            segmentation = segmentations[0]
            # return the Segmentation
            if return_string:
                return segmentation.final
            else:
                return segmentation
        else:
            # no Segmentation; return the Sentence
            if return_string:
                return s.original
            else:
                return s
    elif html:
        if segmentations:
            segmentation = segmentations[0]
            return segmentation.segments, segmentation.get_segment_html()
        return [], s.get_html()
    elif segmentations:
        return segmentations
    return s

def make_document(gui, text, html=False):
    """
    Create a Mitmita Document object with the source text, which
    could be a word, sentence, or document.
    """
    print("CREATING NEW Document INSTANCE.")
    session = gui.session
    d = iwqet.Document(gui.source, gui.target, text, proc=True, session=session)
    if html:
        d.set_html()
    gui.doc = d
    gui.init_doc()
#    return d

def quit(session=None):
    """Quit the session (and the program), cleaning up in various ways."""
    for language in Language.languages.values():
        # Store new cached analyses or generated forms for
        # each active language, but only if there is a current session/user.
        language.quit(cache=session)
#    if session:
#        session.quit()
    print("New items in session {} before committing: {}".format(db.session, db.session.new))
    db.session.commit()

def make_session(source, target, user, create_memory=False, use_anon=True):
    """
    Create an instance of the Session or Memory class for the given user.
    """
#    User.read_all()
#    if isinstance(user, str):
#        # Get the user from their username
#        user = User.users.get(user)
    if use_anon and not user:
        user = get_human('anon')
#        user = User.get_anon()
    username = user.username
    if create_memory:
        session = iwqet.Memory.recreate(user=username)
    elif user:
        session = iwqet.Session(source=source, target=target, user=user)
    return session

## DB functions

def make_dbtext(content, language,
                name='', domain='በያይነቱ', title='',
                description='', segment=False):
    """
    Create a Text database object with the given content and
    language, returning its id.
    """
    text = Text(content=content, language=language,
                name=name, domain=domain, title=title,
                description=description, segment=segment)
#    db.session.add(text)
#    db.session.commit()
    return text

def make_text(gui, textid):
    """Initialize with the Text object specified by textid."""
    textobj = get_text(textid)
    nsent = len(textobj.segments)
    html, html_list = get_doc_text_html(textobj)
    gui.init_text(textid, nsent, html, html_list)

def get_doc_text_html(text):
    if not text.segments:
        return
    html = "<div id='doc'>"
    seghtml = [s.html for s in text.segments]
    html += ''.join(seghtml)
    html += "</div>"
    return html, seghtml

def sentences_from_text(text=None, textid=-1, source=None, target=None):
    """Get a list of sentences from the Text object."""
    if not text and textid == -1:
        return
    text = text or get_text(textid)
    sentences = []
    for textseg in text.segments:
        original = textseg.content
        tokens = [tt.string for tt in textseg.tokens]
        sentence = Sentence(original=original, tokens=tokens,
                            language=source, target=target)
        sentences.append(sentence)
    return sentences

def sentence_from_textseg(textseg=None, source=None, target=None, textid=None,
                          oindex=-1):
    """
    Create a Sentence object from a DB TextSeg object, which is either
    specified explicitly or accessed via its index within a Text object.
    THERE'S SOME DUPLICATION HERE BECAUSE SENTENCE OBJECTS WERE ALREADY
    CREATED WHEN THE Text OBJECT WAS CREATED IN THE DB.
    """
#    print("Creating sentence from textseg, source={}".format(source))
    textseg = textseg or get_text(textid).segments[oindex]
    original = textseg.content
    tokens = [tt.string for tt in textseg.tokens]
    return Sentence(original=original, tokens=tokens, language=source,
                    target=target)

def make_translation(text=None, textid=-1, accepted=None,
                     translation='', user=None):
    """
    Create a Translation object, given a text, a user (translator), and a
    list of sentence translations from the GUI. There may be missing
    translations.
    """
    text = text or get_text(textid)
    trans = Translation(text=text, translator=user)
    db.session.add(trans)
    sentences = accepted if any(accepted) else translation
    # Sentence translations accepted separately
    for index, sentence in enumerate(sentences):
        if sentence:
            ts = TraSeg(content=sentence, translation=trans, index=index)
    print("Added translation {} to session {}".format(trans, db.session))
    db.session.commit()
    return trans

def create_human(form):
    """
    Create and add to the text DB an instance of the Human class,
    based on the form returned from tra.html.
    """
    level = form.get('level', 1)
    level = int(level)
    human = Human(username=form.get('username', ''),
                  password=form.get('password'),
                  email=form.get('email'),
                  name=form.get('name', ''),
                  level=level)
    db.session.add(human)
    db.session.commit()
    return human

def get_humans():
    """Get all existing Human DB objects."""
    return db.session.query(Human).all()

def get_human(username):
    """Get the Human DB object with the given username."""
    humans = db.session.query(Human).filter_by(username=username).all()
    if humans:
        if len(humans) > 1:
            print("Warning: {} users with username {}!".format(len(humans), username))
        return humans[0]

def get_domains_texts():
    """
    Return a list of domains and associated texts and a dict of texts by id.
    """
    dom = dict([(d, []) for d in DOMAINS])
    for text in db.session.query(Text).all():
        d1 = text.domain
        id = text.id
        dom[d1].append((id, text.title))
    # Alphabetize text titles
    for texts in dom.values():
        texts.sort(key=lambda x: x[1])
    dom = list(dom.items())
    # Alphabetize domain names
    dom.sort()
    return dom

def get_text(id):
    """Get the Text object with the given id."""
    return db.session.query(Text).get(id)

# Import views. This has to appear after the app is created.
import iwqet.views
