#
#   MDT utility functions.
#
########################################################################
#
#   This file is part of the HLTDI L^3 project
#   for parsing, generation, translation, and computer-assisted
#   human translation.
#
#   Copyleft (C) 2014, 2016, 2017, 2018 HLTDI, PLoGS <gasser@indiana.edu>
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

# 2014.07.08
# -- Created

import unicodedata, re, datetime, docx
from sys import getsizeof, stderr
from itertools import chain
from collections import deque
try:
    from reprlib import repr
except ImportError:
    pass

# Time constants
TIME_FORMAT = "%d.%m.%Y/%H:%M:%S:%f"
# Time format without microseconds; used in Session and Memory ID and for User creation and update times
SHORT_TIME_FORMAT = "%d.%m.%Y/%H:%M:%S"
# Format without punctuation, for memory filenames (sortable by date created)
MEM_SHORT_TIME_FORMAT = "%Y%m%d%H%M%S"

ZERO_TIME = datetime.timedelta()
TIME0 = datetime.datetime.utcnow()

## Compiled regexs
# Whether the string is capitalized
ISCAP_RE = re.compile(r"^[-–¿¡(\"\'‶“‘$]*[A-ZÀ-Ⱬ]")
# Capitalize the string
CAP_RE = re.compile(r"^([-–¿¡(\"\'‶“‘$]*)(\w)")
CLEAN_RE = re.compile(r"\s+([.,;:?!)”″’%¶])")

## Documents
def text_from_doc(path):
    try:
        if path.endswith('.docx'):
            doc = docx.Document(path)
            text = [para.text for para in doc.paragraphs]
            # Join paragraphs with something other than
            text = '\n\n'.join(text)
            return text
        else:
            with open(path, encoding='utf8') as file:
                return ''.join(file.readlines())
    except IOError:
        print("¡Archivo no encontrado!")
#    except docx.opc.exceptions.PackageNotFoundError:
#        print("No se pudo encontrar el archivo {}".format(path))

## Strings

def clean_sentence(string, capitalize=True):
    """Clean up sentence for display in interface."""
    # Delete spaces before .,;?!, etc.
    string = CLEAN_RE.sub(r"\1", string)
    # Delete spaces after ("', etc.
    string = re.sub(r"([-–]?[¿¡(\"‶“‘$])\s+", r"\1", string)
    # Delete initial spaces after dashes (others?)
    string = re.sub(r"^([-–]+)\s+", r"\1", string)
#        print("Cleaned {}, capitalize? {}".format(string, capitalize))
    if capitalize:
        string = capitalize_string(string)
    return string

def is_capitalized(string):
    """True if the first non-punctuation character in the string is capitalized."""
    return ISCAP_RE.match(string)

def capitalize_string(string):
    """Capitalize the first character following sentence initial punctuation."""
    return CAP_RE.sub(lambda m: m.group(1) + m.group(2).upper(), string)

def remove_control_characters(s):
    """Returns string s with unicode control characters removed."""
    return "".join(ch for ch in s if unicodedata.category(ch) not in ("Cf", "Cs", "Co", "Cn"))

## Time
def get_time(string=True):
    time = datetime.datetime.utcnow()
    if string:
        return time2shortstr(time)
    return time

def get_time_since0(time):
    return time - TIME0

def time2str(time):
    return time.strftime(TIME_FORMAT)

def time2shortstr(time):
    return time.strftime(SHORT_TIME_FORMAT)

def str2time(string):
    return datetime.datetime.strptime(string, TIME_FORMAT)

def shortstr2time(string):
    return datetime.datetime.strptime(string, SHORT_TIME_FORMAT)

## Sequence processing

def allcombs(seqs):
    """Returns a list of all sequences consisting of one element from each of seqs.
    This could also be done with itertools.product."""
    if not seqs:
        return []
    res = [[x] for x in seqs[0]]
    for item in seqs[1:]:
        for i in range(len(res)-1, -1, -1):
            rr = res[i]
#            print(" {} | {} | {}".format(i, rr, [(rr + [itemitem]) for itemitem in item]))
            res[i:i+1] = [(rr + [itemitem]) for itemitem in item]
    return res

def firsttrue(predicate, seq):
    """First element of sequence for which predicate is True. None otherwise."""
    for x in seq:
        px = predicate(x)
        if  px:
            return x

### Measure the size of an object (recursively)

def total_size(o, handlers={}, verbose=False):
    """ Returns the approximate memory footprint an object and all of its contents.

    Automatically finds the contents of the following builtin containers and
    their subclasses:  tuple, list, deque, dict, set and frozenset.
    To search other containers, add handlers to iterate over their contents:

        handlers = {SomeContainerClass: iter,
                    OtherContainerClass: OtherContainerClass.get_elements}
    Example call
    d = dict(a=1, b=2, c=3, d=[4,5,6,7], e='a string of chars')
    print(total_size(d, verbose=True))
    """
    dict_handler = lambda d: chain.from_iterable(d.items())
    all_handlers = {tuple: iter,
                    list: iter,
                    deque: iter,
                    dict: dict_handler,
                    set: iter,
                    frozenset: iter,
                   }
    all_handlers.update(handlers)     # user handlers take precedence
    seen = set()                      # track which object id's have already been seen
    default_size = getsizeof(0)       # estimate sizeof object without __sizeof__

    def sizeof(o):
        if id(o) in seen:       # do not double count the same object
            return 0
        seen.add(id(o))
        s = getsizeof(o, default_size)

        if verbose:
            print(s, type(o), repr(o), file=stderr)

        for typ, handler in all_handlers.items():
            if isinstance(o, typ):
                s += sum(map(sizeof, handler(o)))
                break
        return s

    return sizeof(o)
