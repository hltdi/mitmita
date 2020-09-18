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

class FSSet(set, FS):
    """Sets of feature structures."""

    def __init__(self, *items):
        '''
        Create a feature structure set from items, normally a list of
        feature structures or strings.
        '''
        # This may still be needed for unpickling, when items is a tuple or a list of FeatStructs
        if len(items) > 0 and isinstance(items[0], (list, set)):
            items = items[0]
        if not isinstance(items, set):
            items = [(FeatStructParser().parse(i) if isinstance(i, str) else i) for i in items]
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

    def copyFSS(self):
        return FSSet(self.copy())

    def union(self, fsset):
        """Override set union method by casting result to FSSet."""
        res = set.union(self, fsset)
        return FSSet(res)

    def removeFS(self, FS):
        """
        Remove the FS from all FSs in the set, returning the new FSSet
        (as a list!).
        """
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

    def u(self, f, strict=False, verbose=False):
        """Unify this FSSet with either another FSSet or a FeatStruct."""
        if isinstance(f, FSSet):
            return self.unify(f)
        else:
            return self.unify_FS(f, strict=strict, verbose=verbose)

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
        """
        Attempt to unify this FSSet with a simple FeatStruct instance,
        basically filter the FeatStructs in the set by their unification
        with fs. Pretty much like FSSet.unify(). If list is True,
        return a list of matching FeatStructs or 'fail'.
        """
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
#            print("result1 {}".format(result1.__repr__()))
#            print("result2 {}".format(result2.__repr__()))
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
        """
        Similar to FeatStruct.agree(). Change values of agrs features in
        target to agree with some member(s) of FSSet.
        Ignore features that don't agree (rather than failing) unless
        force is True.
        """
        agr_pairs = agrs.items() if isinstance(agrs, dict) else agrs
        for fs in list(self):
            vals = []
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
#            print("vals {}".format(vals))
#            print("target {}, type {}".format(target.__repr__(), type(target)))
            for f, v in vals:
                if isinstance(target, FeatStruct):
                    target[f] = v
                else:
                    # target is an FSSet
                    new_target = set()
                    for i, fs in enumerate(target):
                        fs = fs.unfreeze()
                        fs[f] = v
                        fs.freeze()
                        new_target.add(fs)
#                    print(" added {}".format(v))
                    target = FSSet(new_target)
#                    print(" new target {}".format(target))
        return target

    def agree_with(self, source, force=False):
        """
        Force self (actually return a changed copy) to agree with source
        (a FeatStruct).
        """
        fss = set()
        for fs in list(self):
            for srcfeat, srcval in source.items():
                fs = FeatStruct.force_set(fs, srcfeat, srcval)
            fs.freeze()
            fss.add(fs)
        return FSSet(fss)

    def agree_FSS(self, target, agrs, force=False, freeze=True):
        """Return an FSSet consisting of a copy of target agreeing on agrs features for each FeatStruct in self."""
        agr_pairs = agrs.items() if isinstance(agrs, dict) else agrs
        new_target = set()
        for fs in list(self):
            if isinstance(target, FSSet):
                targets1 = [target_fs.copy(True) for target_fs in target]
            else:
                targets1 = [target.copy(True)]
            for target1 in targets1:
                vals = []
                for src_feat, targ_feat in agr_pairs:
                    if src_feat in fs:
                        src_value = fs[src_feat]
                        if targ_feat not in target1:
                            vals.append((targ_feat, src_value))
                        else:
                            targ_value = target1[targ_feat]
                            u = simple_unify(src_value, targ_value)
                            if u == 'fail':
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

        to_remove = []
        to_add = []

        for fs in self:
            if fs.frozen():
                fs1 = fs.unfreeze()
                fs1.update_inside(features)
                fs1.freeze()
                to_remove.append(fs)
                to_add.append(fs1)
#                self.remove(fs)
#                self.add(fs1)
            else:
                fs.update_inside(features)
        for x in to_remove:
            self.remove(x)
        for x in to_add:
            self.add(x)

    def get(self, feature, default=None):
        """Get the value of the feature in the first FeatStruct that has one."""
        for fs in self:
            value = fs.get(feature)
            if value != None:
                return value
        return default

    ### Type conversion

    def to_featstruct(self):
        """Convert this FSSet to a FeatStruct instance by taking the first element in it."""
        if len(self) > 0:
            return list(self)[0]
        return TOP

    # @staticmethod
    # def from_FS(fs, length=1):
    #     """
    #     Return a FSSet instance of length length with a copy of
    #     FeatStruct fs as each element.
    #     """
    #     if length == 1:
    #         return FSSet(fs)
    #     fslist = []
    #     for index in range(length):
    #         fslist.append(fs.copy())
    #     return FSSet(fslist)

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

    def upd(self, features=None):
        """
        Return an updated FSSet agreeing with features in features.
        """
        return FSSet.update(self, features)

    @staticmethod
    def update(fsset, feats):
        """Return a new fsset with feats updated to match each fs in fsset."""
        fslist = []
        for fs in fsset:
            fs_copy = feats.copy()
            fs_copy.update(fs)
            fslist.append(fs_copy)
        for index, fs in enumerate(fslist):
            if isinstance(fs, dict):
                fslist[index] = FeatStruct(fs)
            else:
                fs.freeze()
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

    @staticmethod
    def compareFSS(fss_list):
        """Compare feature values in a list of FSSs, first reducing each to a single FS with all shared values."""
        fs_list = [FSSet.FSS2FS(fss) for fss in fss_list]
        shared, diff = FSSet.compare(fs_list)
        return diff

    @staticmethod
    def FSS2FS(fss):
        """Convert the FSSet to a FeatStruct that includes the features shared across the set of FeatStructs
        in the FSSet."""
        fs = FeatStruct()
        fsslist = list(fss)
        fs0 = fsslist[0]
        fss_rest = fsslist[1:]
        for f1 in fs0.keys():
            fs01 = fs0.get(f1)
            shared = True
            for fs2 in fss_rest:
                if f1 not in fs2:
                    shared = False
                    break
                fs21 = fs2.get(f1)
                if fs01 != fs21:
                    shared = False
                    break
            if shared:
                # Each FS has a value and they're all equal, so add this to
                # the shared values
                fs[f1] = fs01
        return fs

    @staticmethod
    def compare(fss):
        """Compare feature values in the FS set, returning a pair of dicts: shared values, different values.
        fss can also be a list of FeatStruct instances."""
        if len(fss) == 1:
            return list(fss)[0], {}
        feats = set()
        shared = {}
        diffs = {}
        for fs in fss:
            feats.update(list(fs.keys()))
        for f in feats:
            # values of features f in all FSs
            values = [fs.get(f, None) for fs in fss]
            v0 = values[0]
            same = True
            index = 1
            while same and index < len(values):
                v = values[index]
                if v != v0:
                    same = False
                index += 1
            if same:
                shared[f] = v0
            else:
                diffs[f] = values
        return shared, diffs

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
