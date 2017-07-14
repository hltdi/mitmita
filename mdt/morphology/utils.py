"""
This file is part of MDT.

    Copyleft 2015, 2016, 2017. HLTDI, PLoGS <gasser@indiana.edu>
   
    Mainumby is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    Mainumby is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with MDT.  If not, see <http://www.gnu.org/licenses/>.
--------------------------------------------------------------------

Miscellaneous utility functions.
"""

import functools

VERBOSITY = 0

COMMENT = '#'

### Segmentation of words into graphemes/phonemes.

def segment(word, units, correct=True):
    res = []
    pos = 0
    while pos < len(word):
        ch = word[pos]
        if ch in units[0]:
            res.append(ch)
            pos += 1
        else:
            sublists = units[1]
            if ch in sublists:
                sublist = sublists[ch]
                if pos < len(word) - 1 and ch + word[pos + 1] in sublist:
                    if pos < len(word) - 2 and ch + word[pos + 1:pos + 3] in sublist:
                        res.append(ch + word[pos + 1:pos + 3])
                        pos += 3
                    else:
                        res.append(ch + word[pos + 1])
                        pos += 2
                else:
                    res.append(ch)
                    pos += 1
            elif correct:
                print(ch, 'in', word, 'is not an acceptable character')
                return
            else:
                res.append(ch)
                pos += 1
    return res
def reduce_lists(lists):
    '''Flatten a list of lists (doesn't mutate lists).'''
    return functools.reduce(lambda x, y: x + y, lists) if lists else []

def del_suffix(string, sufstart, last = True):
    '''String without everything after the last (or first) occurrence of sufstart.'''
    sufpos = string.rfind(sufstart) if last else string.find(sufstart)
    if sufpos >= 0:
        return string[:sufpos]
    else:
        return string

def starts(subseq, seq):
    '''Does the subseq begin the seq?'''
    if len(subseq) > len(seq):
        return False
    else:
        for i in range(len(subseq)):
            if subseq[i] != seq[i]:
                return False
        return True

def seq_index(subseq, seq, pos = 0):
    '''Index of the subseq within the seq, -1 if it's not there at all.'''
    if subseq[0] in seq:
        start = seq.index(subseq[0])
        if starts(subseq, seq[start:]):
            return start + pos
        else:
            return seq_index(subseq, seq[start+1:], start)
    else:
        return -1

def split_at(string, *positions):
    '''Split string into list at positions.'''
    result = []
    index = 0
    for p in positions:
        result.append(string[index:p])
        index = p
    result.append(string[index:])
    return result

def every(predicate, seq):
    """True if every element of seq satisfies predicate.
    >>> every(callable, [min, max])
    1
    >>> every(callable, [min, 3])
    0
    """
    for x in seq:
        if not predicate(x): return False
    return True

def some(predicate, seq):
    """If some element x of seq satisfies predicate(x), return predicate(x).
    >>> some(callable, [min, 3])
    1
    >>> some(callable, [2, 3])
    0
    """
    for x in seq:
        px = predicate(x)
        if  px: return px

def dict_partkey(dct, key):
    '''Value for a key that's contained in the dct key.  None if there is none.'''
    for k, v in dct.items():
        if key in k:
            return v
