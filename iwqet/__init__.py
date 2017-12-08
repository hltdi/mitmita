# Mit'mit'a. Parsing and translation with minimal dependency grammars.
#
########################################################################
#
#   This file is part of the Mainumby project within the PLoGS metaproject
#   for parsing, generation, translation, and computer-assisted
#   human translation.
#
#   Copyleft 2015, 2016, 2017 HLTDI, PLoGS <gasser@indiana.edu>
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

__all__ = ['views', 'record']
#  not needed for now: 'learn'

from flask import Flask, url_for, render_template

## train imports sentence
from mdt.train import *

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
from mdt.morphology import *
from iwqet.record import *
# from . import db

## Instantiate the Flask class to get the application
app = Flask(__name__)
app.config.from_object(__name__)

LANGUAGE_DIR = os.path.join(os.path.dirname(__file__), 'languages')

def get_language_dir(abbrev):
    return os.path.join(LANGUAGE_DIR, abbrev)

def load(source='eng', target='amh', groups=None):
    """Load a source and a target language, given as abbreviations.
    Read in groups for source language, including target language translations at the end.
    If train is True, load the analysis rather than generation FSTs for the target language.
    If the languages are already loaded, don't load them."""
    srclang = Language.languages.get(source)
    targlang = Language.languages.get(target)
    loaded = False
    srcuse = mdt.SOURCE
    targuse = mdt.TARGET
    if srclang and targlang and srclang.use == srcuse and targlang.use == targuse:
        loaded = True
    else:
#        try:
        srcdir = get_language_dir(source)
        targdir = get_language_dir(target)
        srcpath = os.path.join(srcdir,  source + '.lg')
        srclang = Language.read(srcpath, use=srcuse, directory=srcdir)
        print("Source language {} loaded".format(srclang))
        targpath = os.path.join(targdir, target + '.lg')
        targlang = Language.read(targpath, use=targuse, directory=targdir)
        print("Target language {} loaded".format(targlang))
        if not srclang:
            print("Source language failed to load!")
            return
        if not targlang:
            print("Target language failed to load!")
            return
#        except IOError:
#        if not srclang:
#            print("At least one of these languages doesn't exist.")
#            return
    # Load groups for source language now
    if not loaded:
        srclang.read_groups(files=groups, target=targlang)
        srclang.read_ms(target=targlang)
    return srclang, targlang

#def load(source='spa', target='grn'):
#    """Load source and target languages for translation."""
#    print("Attempting to load {} and {}".format(source, target))
#    return iwqet.Language.load_trans(source, target)

def seg_trans(sentence, source, target, session=None, verbosity=0):
    """Translate sentence and return marked-up sentence with segments colored.
    So far only uses first solution."""
    sentence.initialize(ambig=True, verbosity=verbosity)
    sentence.solve(translate=True, all_sols=False, all_trans=True, interactive=False, verbosity=verbosity)
    if sentence.solutions:
        solution = sentence.solutions[0]
        solution.get_segs()
        return solution.segments, solution.get_seg_html()
    else:
        return [], sentence.get_html()

def make_document(source, target, text, session=None):
    """Create an Mainumby Document object with the text."""
    d = iwqet.Document(source, target, text, proc=True, session=session)
    return d

def quit(session=None):
    """Quit the session (and the program), cleaning up in various ways."""
    for language in Language.languages.values():
        # Store new cached analyses or generated forms for
        # each active language, but only if there is a current session/user.
        language.quit(cache=session)
    if session:
        session.quit()

def start(source, target, user):
    """Initialize a run. Create a session if there's a user."""
#    print("Starting {}, {}, {}".format(source, target, user))
    # Read in current users so that we can find the current user and
    # check for username overlap if a new account is created
    init_users()
#    User.read_all()
    if isinstance(user, str):
        # Get the user from their username
        user = User.users.get(user)
    if user:
        return iwqet.Session(source=source, target=target, user=user)

## Users and Sessions
def init_users():
    # Read in current users before login.
    User.read_all(path=get_users_path())

def get_user(username):
    """Find the user with username username."""
    print("Looking for user with username {}".format(username))
    return User.get_user(username)

def create_user(dct):
    """Create a user from the dict of form values from login.html."""
    return User.dict2user(dct)

def get_users_path():
    return os.path.join(SESSIONS_DIR, 'all.usr')

def get_user_path(user):
    filename = "{}.usr".format(user.username)
    return os.path.join(SESSIONS_DIR, filename)

def save_record(user, record):
    """Write the session feedback to the user's file."""
    with open(get_user_path(user), 'a', encoding='utf8') as file:
        record.write(file=file)

# Import views. This has to appear after the app is created.
import iwqet.views

