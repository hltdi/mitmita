# MDT. Parsing and translation with minimal dependency grammars.
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
#   along with this program. If not, see <http://www.gnu.org/

__all__ = ['language', 'entry', 'ui', 'constraint', 'variable', 'sentence', 'cs', 'utils', 'record', 'train', 'tag']
#  not needed for now: 'learn'

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

## morphology a package; imports morphology.morpho
### which imports morphology.fst
#### which imports morphology.semiring
##### which imports morphology.fs, morphology.utils
###### fs imports morphology.logic, morphology.internals
from .morphology import *

from iwqet.record import *
# from . import db


