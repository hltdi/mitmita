########################################################################
#
#   This file is part of the MDT project.
#
#   Copyleft 2014, 2016, 2017; HLTDI, PLoGS <gasser@indiana.edu>
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
#    Author: Michael Gasser <gasser@indiana.edu>
#
# 2016.06.01
# -- New functions for unification and agreement, extending those in FeatStruct.
#    Needed for features of merged nodes.
# 2017.04.24
# -- Added unify_FS method and cast option for unfreeze (otherwise it
#    returns a list FeatStructs).
# 2017.05.10
# -- Added method for getting a feature value within a FSSet
# -- Overriding union for FSSet so it returns an FSSet
# 2017.05.19
# -- Fixed unify_FS() so it can "fail".
# -- FSSet constructor modified so it never contains tuples
# -- FSSet.update_inside(), corresponding to FeatStruct.update_inside()

from .fs import *
from .utils import *

######################################################################
# FeatStruct stuff
######################################################################

class FSSet(set):
    """Sets of feature structures."""

    def __init__(self, *items):
        '''Create a feature structure set from items, normally a list of feature structures or strings.'''
        # This may still be needed for unpickling, when items is a tuple or a list of FeatStructs
        if len(items) > 0 and isinstance(items[0], (list, set)):
            items = items[0]
        if not isinstance(items, set):
            items = [(FeatStructParser().parse(i) if (isinstance(i, str) or isinstance(i, str)) else i) for i in items]
            # Freeze each feature structure
            for index, itm in enumerate(items):
                if isinstance(itm, FeatStruct):
                    itm.freeze()
                else:
                    # itm must be a dict
                    items[index] = FeatStruct(itm)
        set.__init__(self, items)

    def __repr__(self):
        string = ''
        for i, fs in enumerate(self):
            string += fs.__repr__()
            if i < len(self) - 1:
                string += ';'
        return string

    def short_print(self):
        print(self.__repr__())

    def union(self, fsset):
        """Override set union method by casting result to FSSet."""
        res = set.union(self, fsset)
        return FSSet(res)

    def removeFS(self, FS):
        """Remove the FS from all FSs in the set, returning the new FSSet (as a list!)."""
        fsset = self.unfreeze()
        to_remove = []
        for fs in fsset:
            for key in list(FS.keys()):
                # Assume there's only one level
                fs.pop(key)
            if not fs:
                # Nothing left in it; remove it
                to_remove.append(fs)
        for fs in to_remove:
            fsset.remove(fs)
        return fsset

    def unify(self, fs2):
        """Unify this FSSet with another one."""
        result1 = [simple_unify(f1, f2) for f1 in list(self) for f2 in list(fs2)]
        if every(lambda x: x == TOP, result1):
            # If everything unifies to TOP, return one of them
            return TOPFSS
        else:
            # Get rid of all instances of TOP and unification failures
            return FSSet(*filter(lambda x: x != 'fail', result1))

    def unify_FS(self, fs, strict=False, verbose=False):
        """Attempt to unify this FSSet with a simple FeatStruct instance, basically filter
        the FeatStructs in the set by their unification with fs. Pretty much like FSSet.unify()."""
        # This is a list of the unifications of the elements of self with fs
        result1 = [simple_unify(f1, fs, strict=strict, verbose=verbose) for f1 in list(self)]
        if every(lambda x: x == TOP, result1):
            return TOPFSS
        else:
            # All FeatStructs in self that unify with fs
            result2 = list(filter(lambda x: x != 'fail', result1))
            if verbose:
                print("unify_FS: unifying {} with {}, result {}".format(self, fs.__repr__(), result2))
            if not result2:
                # None of the FeatStructs in self unifies with fs
                return 'fail'
            return FSSet(*result2)

    @staticmethod
    def unify_all(fssets):
        """The FSSet resulting from successively unifying a list of FSSets."""
#        print("Semiring unifying all FSSets: {}".format(fssets))
        if not fssets:
            return TOPFSS
        elif len(fssets) == 1:
            return fssets[0]
        else:
            res = fssets[0].unify(fssets[1])
            if res == 'fail':
                return 'fail'
            else:
                return FSSet.unify_all([res] + fssets[2:])

    def agree(self, target, agrs, force=False):
        """Similar to FeatStruct.agree(). Change values of agrs features in target to agree with some member(s) of FSSet.
        Ignore features that don't agree (rather than failing) unless force is True."""
        agr_pairs = agrs.items() if isinstance(agrs, dict) else agrs
        for fs in list(self):
            vals = []
#            fail = False
            for src_feat, targ_feat in agr_pairs:
                if src_feat in fs:
                    src_value = fs[src_feat]
                    if targ_feat not in target:
                        vals.append((targ_feat, src_value))
                    else:
                        targ_value = target[targ_feat]
                        u = simple_unify(src_value, targ_value)
                        if u == 'fail':
                            if force:
                                vals.append((targ_feat, src_value))
                            else:
                                # Ignore this feature
                                continue
                        else:
                            vals.append((targ_feat, u))
#            if fail:
#                continue
#            print("Changing {} in {}".format(vals, target.__repr__()))
            for f, v in vals:
                target[f] = v

    def agree_FSS(self, target, agrs, force=False, freeze=True):
        """Return an FSSet consisting of a copy of target agreeing on agrs features for each FeatStruct in self."""
        agr_pairs = agrs.items() if isinstance(agrs, dict) else agrs
        new_target = set()
#        print("Agr pairs {}".format(agr_pairs))
        for fs in list(self):
            if isinstance(target, FSSet):
                targets1 = [target_fs.copy(True) for target_fs in target]
            else:
                targets1 = [target.copy(True)]
            for target1 in targets1:
                vals = []
#                print("Target 1 {}, fs {}".format(target1.__repr__(), fs.__repr__()))
                for src_feat, targ_feat in agr_pairs:
#                    print("  Src feat {}, targ feat {}".format(src_feat, targ_feat))
                    if src_feat in fs:
                        src_value = fs[src_feat]
                        if targ_feat not in target1:
                            vals.append((targ_feat, src_value))
                        else:
                            targ_value = target1[targ_feat]
#                            print("    Src value {}, targ value {}".format(src_value, targ_value))
                            u = simple_unify(src_value, targ_value)
                            if u == 'fail':
#                                print("src feat {}/{} doesn't agree with targ feat {}/{}".format(src_feat, src_value, targ_feat, targ_value))
                                if force:
                                    vals.append((targ_feat, src_value))
                                else:
                                    # Ignore this feature
                                    continue
                            else:
                                vals.append((targ_feat, u))
                for f, v in vals:
                    target1[f] = v
                if freeze:
                    target1.freeze()
                new_target.add(target1)
        return FSSet(new_target)

    @staticmethod
    def mutual_agree(source, target, agrs):
        """Source and target are lists of sets of unfrozen FeatStructs, not FSSets.
        Make all FSs target agree with all FSs in self and FSs in sself agree with FSs in target
        on features specified in agrs dict or list of pairs. Features can be of the form x|y, where
        y is a feature within the feature x."""
        for fs1 in source:
            for fs2 in target:
                agree1 = fs1.mutual_agree(fs2, agrs)
                if agree1 == 'fail':
                    return 'fail'
        return FSSet(*source), FSSet(*target)

    def update_inside(self, features=None):
        """
        Based on update_inside for FeatStruct. Replaces features at the deepest level.
        """
        if features is None:
            items = ()
        else:
            items = features.items()

        for fs in self:
            if fs.frozen():
                fs1 = fs.unfreeze()
                fs1.update_inside(features)
                fs1.freeze()
                self.remove(fs)
                self.add(fs1)
            else:
                fs.update_inside(features)

    def get(self, feature, default=None):
        """Get the value of the feature in the first FeatStruct that has one."""
        for fs in self:
            value = fs.get(feature)
            if value:
                return value
        return default

    def to_featstruct(self):
        """Convert this FSSet to a FeatStruct instance by taking the first element in it."""
        if len(self) > 0:
            return list(self)[0]
        return TOP

    def inherit(self):
        """Inherit feature values for all members of set, returning new set."""
        items = [item.inherit() for item in self]
        return FSSet(*items)

    @staticmethod
    def parse(string):
        """string could be a single FS or several separated by ';'."""
        return FSSet(*[s.strip() for s in string.split(';')])

    @staticmethod
    def cast(obj):
        """Cast object to a FSSet."""
        if isinstance(obj, FSSet):
            return obj
        elif isinstance(obj, FeatStruct):
            return FSSet(obj)
        elif isinstance(obj, (str, str)):
            return FSSet.parse(obj)
        else:
            return TOPFSS

    @staticmethod
    def update(fsset, feats):
        """Return a new fsset with feats updated to match each fs in fsset."""
        fslist = []
        for fs in fsset:
            fs_copy = feats.copy()
            fs_copy.update(fs)
            fslist.append(fs_copy)
        return FSSet(*fslist)

    @staticmethod
    def setfeats(fsset, condition, feature, value):
        """A new FSSet with feature set to value if condition is satisfied."""
        fslist = []
        for fs in fsset:
            if not condition or unify(fs, condition):
                # Copy because it's frozen
                fs_copy = fs.copy()
                fs_copy.setdefault(feature, value)
                fslist.append(fs_copy)
            else:
                fslist.append(fs)
        return FSSet(*fslist)

    def unfreeze(self, cast=False):
        """A copy of the FSSet (as a list unless cast is True!) that is a set of unfrozen FSs."""
        c = [fs.copy(True) for fs in self]
        if cast:
            c = FSSet(c)
        return c

## Feature structure that unifies with anything.
TOP = FeatStruct('[]')
TOP.freeze()
TOPFSS = FSSet(TOP)

class Semiring:

    def __init__(self, addition = None, multiplication = None,
                 in_set = None, zero = None, one = None):
        self.addition = addition
        self.multiplication = multiplication
        self.zero = zero
        self.one = one
        self.in_set = in_set

    def multiply(self, x, y):
        return self.multiplication(x, y)

    def add(self, x, y):
        return self.addition(x, y)

    def is_in_set(self, x):
        return self.in_set(x)

    def parse(self, s):
        """Parse a string into a weight."""
        if not s:
            # Default weight for this SR
            return self.one
        elif self == UNIFICATION_SR:
            return FSSet.parse(s)
        else:
            # Number
            return float(s)

### Three semirings

PROBABILITY_SR = Semiring(addition = lambda x, y: x + y,
                          multiplication = lambda x, y: x * y,
                          in_set = lambda x: isinstance(x, float) and x >= 0.0,
                          zero = 0.0,
                          one = 1.0)

TROPICAL_SR = Semiring(addition = lambda x, y: min([x, y]),
                       multiplication = lambda x, y: x + y,
                       in_set = lambda x: isinstance(x, float),
                       zero = None,  # really +infinity
                       one = 0.0)

### Operations for Unification semiring
def uni_add(x, y):
    return x.union(y)

def uni_mult(x, y):
    return x.unify(y)

def uni_inset(x):
    return isinstance(x, FSSet)

UNIFICATION_SR = Semiring(addition = uni_add,
                          multiplication = uni_mult,
                          in_set = uni_inset,
                          zero = set(),
                          one = TOPFSS)
