#
#   Mainumby constraints.
#
########################################################################
#
#   This file is part of the HLTDI L^3 project
#   for parsing, generation, translation, and computer-assisted
#   human translation.
#
#   Copyright (C) 2014, 2015, 2016 HLTDI <gasser@indiana.edu>
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

# 2014.03.27
# -- Created. Initially just copied from l3xdg/constraint.py.
# 2014.03.29
# -- Fixed cant_precede() so it works with IVars (determined and not).
# 2014.04.03
# -- Created ComplexSetConvexity
# 2014.04.05
# -- Created ComplexUnionSelection
# 2014.04.15
# -- Constraint types used so far:
#    UnionSelection, PrecedenceSelection, ComplexUnionSelection,
#    ComplexSetConvexity, Union, Disjoint, Inclusion
# 2014.04.26
# -- Fixed several bugs in SetPrecedence (needed for TL sequencing).
# 2014.04.30
# -- Eliminated lots of unused constraints.
#    Fixed complex constraints so that sub-constraints are not recorded
#    in their variables.
# 2014.05.04-5
# -- AgrSelection constraint.
# 2014.05.05
# -- ComplexAgrSelection constraint.
#    Generalization of three complex constraints to ComplexConstraint class.
# 2014.05.08
# -- Added Order constraint for ordering indices of sequences, replacing multiple
#    SetPrecedence constraints, and including one additional condition not in
#    SetPrecedence.
# 2014.05.11
# -- Complex constraints make selection variables for indices out of main sel
#    selection variables (groups in Ñe'ẽasa) non-essential once the constraint
#    is entailed.
# 2015.08.05
# -- Fixed a bug in UnionSelection: the constraint was allowed to change a sequence
#    variable in an impossible way, by making the upper bound smaller than the
#    lower cardinality; now this causes failure.
# 2016.06.30
# -- New constraint type: DependencySelection. Two main parameters, one a typical
#    selection variable, the other a list of determined set variables, one for
#    each item being selected from. The dependency variable for each element
#    gives the indices of other elements that must be selected for that element
#    to be selected. Needed for dependencies between groups in Mbojereha.
# 2016.07.25
# -- New constraint type: NAND. Single group variable and two ints (converted to
#    determined integer variables that are actually never used). Group may contain
#    neither, either, but not both ints. Needed from imcompatibilities between
#    groups in Mbojereha.

from .variable import *
# This is imported in another branch too...
from iwqet.morphology.fs import *
import itertools

class Constraint:

    # Constants for outcome of running
    failed = 0
    entailed = 1
    sleeping = 2

    # Constant threshold for lenience
    lenience = .5

    def __init__(self, variables, problem=None, record=True, weight=1):
        self.variables = variables
        self.problem = problem
        self.weight = weight
        if record:
            for var in variables:
                if isinstance(var, DetVar):
                    continue
#                    if problem:
#                        if var not in problem.vrs:
#                            problem.vrs[var] = []
#                        problem.vrs[var].append(self)
                var.constraints.append(self)
        self.name = ''

    def __repr__(self):
        return self.name

    def is_lenient(self):
        return self.weight < Constraint.lenience

    def set_weight(self, weight):
        self.weight = weight

    def get_var(self):
        """The single variable for this constraint."""
        return self.variables[0]

    # Each Constraint type must implement fails(), is_entailed(), and infer().

    def fails(self, dstore=None):
        raise NotImplementedError("{} is an abstract class".format(self.__class__.__name__))

    def is_entailed(self, dstore=None):
        raise NotImplementedError("{} is an abstract class".format(self.__class__.__name__))

    def infer(self, dstore=None, verbosity=0, tracevar=None):
        """Should return state and variables that change."""
        raise NotImplementedError("{} is an abstract class".format(self.__class__.__name__))

    def determine(self, dstore=None, verbosity=0, tracevar=None):
        """Try to determine each variable, returning the set if any determined."""
        det = set()
        for variable in self.variables:
            if not variable.is_determined(dstore=dstore) and \
                    variable.determined(dstore=dstore, constraint=self, verbosity=verbosity) is not False:
                if verbosity and variable in tracevar:
                    print('  {} determining {} at {}'.format(self, variable, variable.get_value(dstore=dstore)))
                det.add(variable)
        return det

    def run(self, dstore=None, verbosity=0, tracevar=[]):
        """Run this constraint during constraint satisfaction."""
        if verbosity > 1:
            print(' Running {}'.format(self))
        determined = self.determine(dstore=dstore, verbosity=verbosity, tracevar=tracevar)
        # Try to determine the variables; if any are determined, go to sleep and return
        # the set of newly determined variables.
        if determined:
            if verbosity > 1:
                print('  Determined variables', determined)
            return Constraint.sleeping, determined
        # Otherwise see if the constraint fails. If it does fail and return the empty set.
        if self.fails(dstore=dstore):
            if verbosity > 1:
                print('  Failed!')
            elif verbosity:
                print('{} failed; weight: {}'.format(self, self.weight))
            return Constraint.failed, set()
        # Otherwise see if the constraint is entailed. If it is, succeed and return the empty set.
        if self.is_entailed(dstore=dstore):
            if verbosity > 1:
                print('  Entailed')
            return Constraint.entailed, set()
        # Otherwise try inferring variable values. Either succeed or sleep and return any changed
        # variables.
        return self.infer(dstore=dstore, verbosity=verbosity, tracevar=tracevar)

    @staticmethod
    def string_set(s):
        """Convenient print name for a set."""
        if len(s) > 10:
            return '{{{0}...{1}}}'.format(min(s), max(s))
        else:
            return '{}'.format(set.__repr__(s))

    def print_vars(self):
        '''Print out components of constraint variables.'''
        for v in self.variables:
            print('{} :: {}'.format(v, v.dstores))

## Primitive basic constraints

# Integer domains

class Member(Constraint):

    def __init__(self, var, domain, problem=None, record=True):
        """
        var: an IVar
        domain: a set of ints
        """
        Constraint.__init__(self, (var,), problem=problem, record=record)
        self.domain = domain
        self.name = '{0}<{1}'.format(self.get_var(), Constraint.string_set(self.domain))

    def fails(self, dstore=None):
        """Is the constraint domain not a superset of the variable's domain?"""
        if not self.domain.issubset(self.get_var().get_domain(dstore=dstore)):
            return True
        return False

    def is_entailed(self, dstore=None):
        """Is the variable's domain a subset of the constraint's domain?"""
        if self.get_var().get_domain(dstore=dstore).issubset(self.domain):
            return True
        return False

    def infer(self, dstore=None, verbosity=0, tracevar=None):
        """The variable's values are restricted to the intersection of
        their current values and the constraint's domain."""
        var = self.get_var()
        # was var.strengthen( ... but there is no strengthen in this version of constraint
        if var.strengthen_upper(self.domain, dstore=dstore, constraint=(verbosity>1 or var in tracevar) and self):
            return Constraint.entailed, {var}
        return Constraint.entailed, set()

# Set domains

class Superset(Constraint):
    """Set variable is constrained to be a superset of subset."""

    def __init__(self, var, subset, problem=None, record=True):
        """
        var:    a SVar
        subset: a set of ints
        """
        Constraint.__init__(self, (var,), problem=problem, record=record)
        self.subset = subset
        self.name = '{0} >= {1}'.format(self.get_var(), Constraint.string_set(self.subset))

    def fails(self, dstore=None):
        """Is the constraint subset not a subset of the var's upper bound?"""
        if not self.subset.issubset(self.get_var().get_upper(dstore=dstore)):
            return True
        return False

    def is_entailed(self, dstore=None):
        """Is the variable's lower bound a superset of the constraint's subset?"""
        if self.get_var().get_lower(dstore=dstore).issuperset(self.subset):
            return True
        return False

    def infer(self, dstore=None, verbosity=0, tracevar=None):
        """The variable's values are restricted to be a superset of the union
        of the current lower bound and subset."""
        var = self.get_var()
        if var.strengthen_lower(self.subset, dstore=dstore,
                                constraint=(verbosity>1 or var in tracevar) and self):
            return Constraint.entailed, {var}
        return Constraint.entailed, set()

class Subset(Constraint):
    """Set variable is constrained to be a subset of superset."""

    def __init__(self, var, superset, problem=None, record=True):
        """
        var:    a SVar
        superset: a set of ints
        """
        Constraint.__init__(self, (var,), problem=problem, record=record)
        self.superset = superset
        self.name = '{0} c= {1}'.format(self.get_var(), Constraint.string_set(self.superset))

    def fails(self, dstore=None):
        """Is the var's lower bound not a subset of the constraint superset?"""
        if not self.get_var().get_lower(dstore=dstore).issubset(self.superset):
            return True
        return False

    def is_entailed(self, dstore=None):
        """Is the variable's upper bound a subset of the constraint's superset?"""
        if self.get_var().get_upper(dstore=dstore).issubset(self.superset):
            return True
        return False

    def infer(self, dstore=None, verbosity=0, tracevar=None):
        """The variable's values are restricted to be a subset of the intersection
        of the current upper bound and superset."""
        var = self.get_var()
        if var.strengthen_upper(self.superset, dstore=dstore,
                                constraint=(verbosity>1 or var in tracevar) and self):
#            print("Subset strengthening upper for {} to {} in {}".format(var, var.get_upper(dstore=dstore), dstore))
#            var.pprint(dstore=dstore)
            return Constraint.entailed, {var}
        return Constraint.entailed, set()

# Set domain variables only

class SetConvexity(Constraint):
    """There must not be any 'holes' in the (single) set variable, which represents
    the positions of the descendants of a node as well as that of the node itself."""

    def __init__(self, var, problem=None, weight=1, record=True):
        """Only one variable, so a special constructor."""
        Constraint.__init__(self, [var], problem=problem, weight=weight, record=record)
        self.var = self.variables[0]
        self.name = '{0} <>'.format(self.var)

    def fails(self, dstore=None):
        """Four ways to fail."""
        # If the variable is determined and has holes...
        if self.var.determined(dstore=dstore, constraint=self) is not False:
            val = self.var.get_value(dstore=dstore)
            # There can't be any holes
            if val:
                val_range = set(range(min(val), max(val)+1))
                if val_range - val:
                    return True
        lower_card = self.var.get_lower_card(dstore=dstore)
        lower = self.var.get_lower(dstore=dstore)
        upper = self.var.get_upper(dstore=dstore)
        if lower:
            # Necessary range includes all values between the minimum and the maximum (inclusive)
            # of the lower bound
            neces_range = set(range(min(lower), max(lower)+1))
            if neces_range - upper:
                # If there's some value in necessary range not in upper bound...
                return True
            # Possible values that are not in necessary range
            possible = upper - neces_range
            # If there's a gap separating max necessary and min possible and too many possible
            # values would need to be discarded...
            if possible and neces_range:
                min_poss = min(possible)
                max_neces = max(neces_range)
                if min_poss - max_neces > 1:
                    if len(upper) - len(possible) < lower_card:
                        return True
        # If there is continuous sequence of integers as long as the lower cardinality...
        if lower_card <= 1:
            return False
        upper_ordered = list(upper)
        upper_ordered.sort()
        last = upper_ordered[0]
        count = 1
        for pos in upper_ordered[1:]:
            if count >= lower_card:
                return False
            if pos - last > 1:
                count = 1
                last = pos
            else:
                count += 1
                last = pos
        if count >= lower_card:
            return False
        return True

    def is_entailed(self, dstore=None):
        """If the variable is determined, or if the lower bound is convex,
        and the upper only adds a single vowel below or above the lower bound."""
        if self.var.determined(dstore=dstore, constraint=self) is not False:
            return True
        lower = self.var.get_lower(dstore=dstore)
        upper = self.var.get_upper(dstore=dstore)
        if not lower:
            return False
        min_lower = min(lower)
        max_lower = max(lower)
        if not set(range(min_lower, max_lower+1)) - lower:
            if min_lower - min(upper) <= 1 and max(upper) - max_lower <= 1:
                return True

        return False

    def infer(self, dstore=None, verbosity=0, tracevar=[]):
        changed = set()
        # If the variable's lower bound is non-empty, every value between
        # the min and max of the lower bound must be in the variable, and
        # there can't be any gaps in the upper bound either.
        v = self.var
        lower = v.get_lower(dstore=dstore)
        if len(lower) > 0:
            upper = v.get_upper(dstore=dstore)
            min_low = min(lower)
            max_low = max(lower)
            # Make the lower bound everything between the min and max
            if v.strengthen_lower(set(range(min_low, max_low+1)),
                                  dstore=dstore, constraint=(verbosity>1 or v in tracevar) and self):
                changed.add(v)
                return Constraint.sleeping, changed

            # Look for gaps in the upper bound
            # Starting at the max of the lower bound...
            max_up = max(upper)
            x = max_low+1
            while x in upper and x < max_up:
                x += 1
            if x < max_up:
                if v.discard_upper(set(range(x, max_up+1)),
                                   dstore=dstore, constraint=(verbosity>1 or v in tracevar) and self):
                    changed.add(v)
                    return Constraint.sleeping, changed
            # Starting at the min of the lower bound...
            min_up = min(upper)
            x = min_low-1
            while x in upper and x > min_up:
                x -= 1
            if x > min_up + 1:
                if v.discard_upper(set(range(min_up, x)),
                                   dstore=dstore, constraint=(verbosity>1 or v in tracevar) and self):
                    changed.add(v)
                    return Constraint.sleeping, changed

        return Constraint.sleeping, changed

class SupersetIntersection(Constraint):
    """Set var S1 is superset of intersection of set vars S2 and S3."""

    def __init__(self, variables, problem=None, weight=1, record=True):
        Constraint.__init__(self, variables, problem=problem,
                            weight=weight, record=record)
        self.name = '{0} >= {1} ^ {2}'.format(self.variables[0], self.variables[1], self.variables[2])

    def fails(self, dstore=None):
        """Is the intersection of the lower bounds of S2 and S3 not a subset of
        the upper bound of S1?"""
        s1 = self.variables[0]
        s2 = self.variables[1]
        s3 = self.variables[2]
        s2_inters_s3 = s2.get_lower(dstore=dstore) & s3.get_lower(dstore=dstore)
        if not s2_inters_s3 <= s1.get_upper(dstore=dstore):
            return True
        # Fail on cardinalities
        if s1.get_upper_card(dstore=dstore) < len(s2_inters_s3):
            return True
        return False

    def is_entailed(self, dstore=None):
        """Is the intersection of the upper bounds of S2 and S3 already a subset of
        the lower bound of S1?"""
        s1 = self.variables[0]
        s2 = self.variables[1]
        s3 = self.variables[2]
        if s2.get_upper(dstore=dstore) & s3.get_upper(dstore=dstore) <= s1.get_lower(dstore=dstore):
            return True
        return False

    def infer(self, dstore=None, verbosity=0, tracevar=[]):
        changed = set()
        # Intersection of lower bound of S2 and S3 is subset of lower bound of S1.
        s1 = self.variables[0]
        s2 = self.variables[1]
        s3 = self.variables[2]
        if s1.strengthen_lower(s2.get_lower(dstore=dstore) & s3.get_lower(dstore=dstore),
                               dstore=dstore, constraint=(verbosity>1 or s1 in tracevar) and self):
            changed.add(s1)
        # Upper bound of S2 and S3 excludes elements which are in the lower bounds of S3 and S2, respectively,
        # but not in the upper bound of S1.
        s1_up = s1.get_upper(dstore=dstore)
        s2_not_s1 = s2.get_lower(dstore=dstore) - s1_up
        s3_not_s1 = s3.get_lower(dstore=dstore) - s1_up
        for x in s3.get_upper(dstore=dstore).copy():
            if x in s2_not_s1:
                if s3.discard_upper(x, dstore=dstore, constraint=(verbosity>1 or s3 in tracevar) and self):
                    changed.add(s3)
        for x in s2.get_upper(dstore=dstore).copy():
            if x in s3_not_s1:
                if s2.discard_upper(x, dstore=dstore, constraint=(verbosity>1 or s2 in tracevar) and self):
                    changed.add(s2)
        # Inference based on cardinalities (from Müller, p. 104)
        s2Us3_card = len(s2.get_upper(dstore=dstore) | s3.get_upper(dstore=dstore))
        s1_up_card = s1.get_upper_card(dstore=dstore)
        s2_low_card = s2.get_lower_card(dstore=dstore)
        s3_low_card = s3.get_lower_card(dstore=dstore)
        if s1.strengthen_lower_card(s2_low_card + s3_low_card - s2Us3_card,
                                    dstore=dstore, constraint=(verbosity>1 or s1 in tracevar) and self):
            changed.add(s1)
        if s2.strengthen_upper_card(s2Us3_card + s1_up_card - s3_low_card,
                                    dstore=dstore, constraint=(verbosity>1 or s2 in tracevar) and self):
            changed.add(s2)
        if s3.strengthen_upper_card(s2Us3_card + s1_up_card - s2_low_card,
                                    dstore=dstore, constraint=(verbosity>1 or s3 in tracevar) and self):
            changed.add(s3)
        if verbosity > 1 and changed:
            print('  Variables {} changed'.format(changed))
        return Constraint.sleeping, changed

class SubsetUnion(Constraint):
    """Set var S1 is subset of union of set vars S2 and S3."""

    def __init__(self, variables, problem=None, propagate=True,
                 weight=1, record=True):
        Constraint.__init__(self, variables, problem=problem, weight=weight, record=record)
        self.name = '{0} c= {1} U {2}'.format(self.variables[0], self.variables[1], self.variables[2])

    def fails(self, dstore=None):
        """Is the union of the upper bounds of S2 and S3 (the biggest it can be)
        not a superset of the lower bound of S1?"""
        s1 = self.variables[0]
        s2 = self.variables[1]
        s3 = self.variables[2]
        s2_union_s3 = s2.get_upper(dstore=dstore) | s3.get_upper(dstore=dstore)
        if not s2_union_s3 >= s1.get_lower(dstore=dstore):
            return True
        # Fail on cardinalities
        if s1.get_lower_card(dstore=dstore) > len(s2_union_s3):
            return True
        return False

    def is_entailed(self, dstore=None):
        """Is the union of the lower bounds of S2 and S3 already a superset of
        the upper bound of S1?"""
        s1 = self.variables[0]
        s2 = self.variables[1]
        s3 = self.variables[2]
        if s2.get_lower(dstore=dstore) | s3.get_lower(dstore=dstore) >= s1.get_upper(dstore=dstore):
            return True
        return False

    def infer(self, dstore=None, verbosity=0, tracevar=[]):
        changed = set()
        # S1 must be a subset of the union of the upper bounds of S2 and S3
        s1 = self.variables[0]
        s2 = self.variables[1]
        s3 = self.variables[2]
        if s1.strengthen_upper(s2.get_upper(dstore=dstore) | s3.get_upper(dstore=dstore),
                               dstore=dstore, constraint=(verbosity>1 or s1 in tracevar) and self):
            changed.add(s1)
        # S2's and S3's lower bounds must contain elements that are in the lower bound of S1 but not
        # S3 and S2, respectively (note: Müller has *lower* bounds of S3 and S2 (Eq. 11.17, p. 105),
        # but this seems too strong).
        s1_not_s2 = s1.get_lower(dstore=dstore) - s2.get_upper(dstore=dstore)
        s1_not_s3 = s1.get_lower(dstore=dstore) - s3.get_upper(dstore=dstore)
        if s3.strengthen_lower(s1_not_s2, dstore=dstore, constraint=(verbosity>1 or s3 in tracevar) and self):
            changed.add(s3)
        if s2.strengthen_lower(s1_not_s3, dstore=dstore, constraint=(verbosity>1 or s2 in tracevar) and self):
            changed.add(s2)
        # Inference based on cardinalities (from Müller, p. 105, but there's apparently
        # a typo; in Eq. 11.19, n1 should be the upper, not the lower bound of S1)
        if s1.strengthen_upper_card(s2.get_upper_card(dstore=dstore) + s3.get_upper_card(dstore=dstore),
                                    dstore=dstore, constraint=(verbosity>1 or s1 in tracevar) and self):
            changed.add(s1)
        if s2.strengthen_lower_card(s1.get_lower_card(dstore=dstore) - s3.get_lower_card(dstore=dstore),
                                    dstore=dstore, constraint=(verbosity>1 or s2 in tracevar) and self):
            changed.add(s2)
        if s3.strengthen_lower_card(s1.get_lower_card(dstore=dstore) - s2.get_lower_card(dstore=dstore),
                                    dstore=dstore, constraint=(verbosity>1 or s3 in tracevar) and self):
            changed.add(s3)
        if verbosity > 1 and changed:
            print('  Variables {} changed'.format(changed))
        return Constraint.sleeping, changed

class SetPrecedence(Constraint):
    """All elements of set variable 1 must precede all elements of set variable 2."""

    def __init__(self, variables, problem=None, weight=1, record=True):
        Constraint.__init__(self, variables, problem=problem,
                            weight=weight, record=record)
        self.name = '{0} << {1}'.format(self.variables[0], self.variables[1])

    # Also used in PrecedenceSelection

    @staticmethod
    def must_precede(svar1, svar2, dstore=None):
        """Is the highest value that can occur in svar1 < the lowest value that can occur in svar2?"""
        v1_upper = svar1.get_upper(dstore=dstore)
        v2_upper = svar2.get_upper(dstore=dstore)
        return v1_upper and v2_upper and (max(v1_upper) < min(v2_upper))

    @staticmethod
    def cant_precede(var1, var2, dstore=None):
        """Is the highest value that must occur in var1 >= the lowest value that must occur in var2?"""
        if not var1.get_upper(dstore=dstore):
            print("Can't precede {}, {}".format(var1, var2))
        # Lower
        if isinstance(var1, IVar):
            v1 = min(var1.get_upper(dstore=dstore))
        elif not var1.get_lower(dstore=dstore):
            return False
        else:
            v1 = max(var1.get_lower(dstore=dstore))
        # Upper
        if isinstance(var2, IVar):
            v2 = max(var2.get_upper(dstore=dstore))
        elif not var2.get_lower(dstore=dstore):
            return False
        else:
            v2 = min(var2.get_lower(dstore=dstore))
        return v1 >= v2
#        return v1_lower and v2_lower and (max(v1_lower) >= min(v2_lower))

    def fails(self, dstore=None):
        """Fail if any of set1's lower bound > any of set2's lower bound."""
        return SetPrecedence.cant_precede(self.variables[0], self.variables[1], dstore=dstore)

    def is_entailed(self, dstore=None):
        """Entailed if everything that can be in set1 precedes anything that can be in set2."""
        return SetPrecedence.must_precede(self.variables[0], self.variables[1], dstore=dstore)

    def infer(self, dstore=None, verbosity=0, tracevar=[]):
        changed = set()
        state = Constraint.sleeping
        v1 = self.variables[0]
        v1_low = v1.get_lower(dstore=dstore)
        v2 = self.variables[1]
        v2_low = v2.get_lower(dstore=dstore)
        # If the lower bound on v1 is not empty, v2 must be a subset of
        # {min(MAX, max(v1 + 1)), ..., MAX}
        if v1_low:
            v2_up_new = range(min([v1.max, max(v1_low) + 1]), v2.max+1)
            if v2.strengthen_upper(v2_up_new, dstore=dstore,
                                   constraint=(verbosity>1 or v2 in tracevar) and self):
                changed.add(v2)
                return state, changed
        # If the lower bound on v2 is not empty, v1 must be a subset of
        # {0, ..., max(0, min(v2_low) - 1)}
        if v2_low:
            v1_up_new = range(0, max([0, min(v2_low) - 1]) + 1)
            if v1.strengthen_upper(v1_up_new, dstore=dstore,
                                   constraint=(verbosity>1 or v1 in tracevar) and self):
                changed.add(v1)
                return state, changed
        # Remove all elements from v1 >= highest possible element in v2
        v1_up = v1.get_upper(dstore=dstore)
        v2_up = v2.get_upper(dstore=dstore)
        v2.max = max(v2_up)
        v1_over = set(itertools.filterfalse(lambda x: x < v2.max, v1_up))
        if v1_over:
            if v1.discard_upper(v1_over, dstore=dstore,
                                constraint=(verbosity>1 or v1 in tracevar) and self):
                changed.add(v1)
                return state, changed
        return state, changed

class Order(Constraint):
    """N int variables, whose values are positions from 0 to n-1."""

    def __init__(self, variables, problem=None, weight=1, record=True):
        Constraint.__init__(self, variables, problem=problem,
                            weight=weight, record=record)
        self.max_value = len(variables) - 1
        self.name = '{0} <...<'.format(self.variables)

    def fails(self, dstore=None):
        """Fail if any determined variable has a value greater than maximum (n-1)
        or if two determined variables have the same value or in any value
        in the range is not in the domain of any variable."""
        det_values = []
        for v in self.variables:
            if v.determined(dstore=dstore, constraint=self) is not False:
                val = v.get_value(dstore=dstore)
                val = list(val)[0]
                if val > self.max_value or val in det_values:
                    return True
                det_values.append(val)
        for i in range(len(self.variables)):
            found = False
            for v in self.variables:
                if i in v.get_upper(dstore=dstore):
                    found = True
                    break
            if not found:
                return True
        return False

    def is_entailed(self, dstore=None):
        """Entailed if all variables are determined."""
        for v in self.variables:
            # Some variable is not determined
            if v.determined(dstore=dstore, constraint=self) is False:
                return False
        return True

    def infer(self, dstore=None, verbosity=0, tracevar=[]):
        """If some value is only in the domain of one variable, determine that variable
        at that value."""
        changed = set()
        state = Constraint.sleeping
        for i in range(len(self.variables)):
            v = None
            for vb in self.variables:
                if i in vb.get_upper(dstore=dstore):
                    if v:
                        # Already a variable that has this value
                        v = None
                        break
                    else:
                        v = vb
            if v:
                if v.determine(i, dstore=dstore,
                               constraint=(verbosity>1 or vb in tracevar) and self):
                    changed.add(v)
                    return state, changed
        return state, changed

class NAND(Constraint):
    """
    The main (set) variable includes neither elem1 or elem2, either elem1 or elem2, but not both elem1 and elem2.
    elem1 and elem2 are ints. This behaves like NAND (alternative denial) with respect to elem1 and elem2, though
    mainvar can contain other values.
    """

    def __init__(self, mainvar=None, elem1=None, elem2=None,
                 problem=None, weight=1, maxset=None, record=True):
        self.v1 = DetIVar('nand_v1', elem1)
        self.v2 = DetIVar('nand_v2', elem2)
        Constraint.__init__(self, [mainvar, self.v1, self.v2],
                            problem=problem, weight=weight, record=record)
        self.mainvar = mainvar
        self.elem1 = elem1
        self.elem2 = elem2
        self.name = '{} = {}|{}'.format(self.mainvar, self.elem1, self.elem2)

    def is_entailed(self, dstore=None):
        """Entailed if
        (1) neither elem1 nor elem2 is in mainvar's upper bound
        (2) elem1 is in mainvar's lower bound and elem2 is not in mainvar's upper bound
        (3) elem2 is in mainvar's lower bound and elem1 is not in mainvar's upper bound
        (4) mainvar is determined.
        """
        if self.mainvar.determined(dstore=dstore, constraint=self) is not False:
            return True
        mainup = self.mainvar.get_upper(dstore=dstore)
        elem1 = self.elem1
        elem2 = self.elem2
        if elem1 not in mainup and elem2 not in mainup:
            return True
        mainlow = self.mainvar.get_lower(dstore=dstore)
        if elem1 in mainlow and elem2 not in mainup:
            return True
        if elem2 in mainlow and elem1 not in mainup:
            return True
        return False

    def fails(self, dstore=None):
        """Fail if both elem1 and elem2 are in mainvar lower bound."""
        mainlow = self.mainvar.get_lower(dstore=dstore)
        if self.elem1 in mainlow and self.elem2 in mainlow:
            return True
        return False

    def infer(self, dstore=None, verbosity=0, tracevar=[]):
        """If one or the other of elem1 and elem2 is in mainvar's lower bound,
        the other must not be in mainvar's upper bound. The constraint is then entailed."""
        changed = set()
        state = Constraint.sleeping
        mainlow = self.mainvar.get_lower(dstore=dstore)
        mainup = self.mainvar.get_upper(dstore=dstore)
        elem1 = self.elem1
        elem2 = self.elem2
        if elem1 in mainlow:
            if self.mainvar.discard_upper(elem2, dstore=dstore,
                                         constraint=(verbosity>1 or self.mainvar in tracevar) and self):
                changed.add(self.mainvar)
                state = Constraint.entailed
                return state, changed
        if elem2 in mainlow:
            if self.mainvar.discard_upper(elem1, dstore=dstore,
                                         constraint=(verbosity>1 or self.mainvar in tracevar) and self):
                changed.add(self.mainvar)
                state = Constraint.entailed
                return state, changed

        return state, changed

# Selection constraint propagators

class Selection(Constraint):
    """Superclass for most selection constraints.

    mainvar: set domain var or int domain var (set var for primitive propagators)
    seqvars: set domain vars, int domain vars, constant sets, or constant ints
             (set var for primitive propagators)
    selvar: set domain var or int domain var (set var for primitive propagators)
    """

    def __init__(self, mainvar=None, selvar=None, seqvars=None,
                 problem=None, weight=1, record=True):
        Constraint.__init__(self, [mainvar, selvar] + seqvars, problem=problem,
                            weight=weight, record=record)
        self.selvar = selvar
        self.mainvar = mainvar
        self.seqvars = seqvars

    def is_entailed(self, dstore=None):
        """Entailed only if all vars are determined.
        """
        if self.mainvar.determined(dstore=dstore, constraint=self) is not False \
           and self.selvar.determined(dstore=dstore, constraint=self) is not False \
           and all([v.determined(dstore=dstore, constraint=self) is not False for v in self.seqvars]):
            return True
        return False

    def infer(self, dstore=None, verbosity=0, tracevar=None):
        """Some rules are common to all Selection subclasses."""

        changed = set()
        state = Constraint.sleeping
        seqvars = self.seqvars
        selvar = self.selvar
        mainvar = self.mainvar

        # If there is only one seqvar, then the main var is constrained to be that value
        # and the selection var has to be {0} or 0
        if len(seqvars) == 1:
            # since there's only one seq var to select, the selection variable has to
            # be {0} or 0
            if selvar.determine(0, dstore=dstore,
                                constraint=(verbosity>1 or selvar in tracevar) and self):
                changed.add(selvar)
            seqvar = seqvars[0]
            if seqvar.determined(dstore=dstore, verbosity=verbosity, constraint=self) is not False:
                if mainvar.determine(seqvar.get_value(dstore=dstore), dstore=dstore,
                                     constraint=(verbosity>1 or mainvar in tracevar) and self):
                    changed.add(mainvar)
                state = Constraint.entailed
            else:
                if mainvar.strengthen_lower(seqvar.get_lower(dstore=dstore), dstore=dstore,
                                            constraint=(verbosity>1 or mainvar in tracevar) and self):
                    changed.add(mainvar)
                if mainvar.strengthen_upper(seqvar.get_upper(dstore=dstore), dstore=dstore,
                                            constraint=(verbosity>1 or mainvar in tracevar) and self):
                    changed.add(mainvar)
##                if mainvar.determined(dstore=dstore, verbosity=verbosity) is not False:
##                    state = Constraint.entailed
            if changed:
                if verbosity > 1:
                    print('  Variables {} changed'.format(changed))
                return state, changed
        # If all of the seqvars are equal to one another and determined and the selection variable must
        # be non-empty, then the main var can be determined (as long as the seqvar value is in its domain)
        if all([v.determined(dstore=dstore, verbosity=verbosity, constraint=self) is not False for v in seqvars]) and \
             selvar.get_lower_card(dstore=dstore) > 0 and seqvars[0].all_equal(seqvars[1:], dstore=dstore):
            seq0_val = seqvars[0].get_value(dstore=dstore)
            if mainvar.determine(seq0_val, dstore=dstore, constraint=(verbosity>1 or mainvar in tracevar) and self):
                changed.add(mainvar)
                state = Constraint.entailed
                if verbosity > 1 and changed:
                    print('  Variables {} changed'.format(changed))
                return state, changed

        return False

    @staticmethod
    def format_seq(seq):
        string = '< '
        for i, elem in enumerate(seq):
            if i != 0:
                string += ', '
            if elem == set():
                string += '{}'
            else:
                string += elem.__repr__()
        return string + ' >'

    @staticmethod
    def format_list(seq):
        string = '['
        for i, elem in enumerate(seq):
            if i != 0:
                string += ', '
            if elem == set():
                string += '{}'
            else:
                string += elem.__repr__()
        return string + ']'

class UnionSelection(Selection):
    '''All variables can be set vars; seq vars can also be int vars.
    Select the union of the selected sets.'''

    def __init__(self, mainvar=None, selvar=None, seqvars=None, problem=None, weight=1,
                 maxset=None, record=True):
        Selection.__init__(self, mainvar=mainvar, selvar=selvar, seqvars=seqvars,
                           problem=problem, weight=weight, record=record)
        self.maxset = maxset or ALL
        self.name = '{0} = U{1} [{2}]'.format(self.mainvar, self.format_seq(self.seqvars), self.selvar)

    def sel_lower(self, dstore=None):
        """Values that must be selected."""
        seq_len = len(self.seqvars)
        selvar_lower = self.selvar.get_lower(dstore=dstore)
        if any([i >= seq_len for i in selvar_lower]):
            return False
        res = set()
        for i in selvar_lower:
            if i < len(self.seqvars):
                res.update(self.seqvars[i].get_lower(dstore=dstore))
        return res

    def fails(self, dstore=None):
        """Fail
        (1) if the lower bound of sel var has indices beyond the length of seq vars
        (2) if the upper bound of mainvar excludes a value that must be in it
        (3) if the lower bound of mainvar includes values that cannot be in the union
            of selected seq vars (upper bounds of seq vars selected by upper bound of
            sel var)
        """
        sel_low = self.sel_lower(dstore=dstore)
        if sel_low is False:
#            print(self, 'fails because of sel_low')
            # This should actually fail but allow it to succeed
            sel_low = set()
        mainupper = self.mainvar.get_upper(dstore=dstore)
        if len(sel_low - self.mainvar.get_upper(dstore=dstore)) > 0:
            return True
        # If the values that must be included in mainvar include values that are excluded
        # from those that can be selected, fail
        mainlower = self.mainvar.get_lower(dstore=dstore)
        selupper = self.selvar.get_upper(dstore=dstore)
        maxsel = set()
        for index, seq in enumerate(self.seqvars):
            if index in selupper:
                sequpper = seq.get_upper(dstore=dstore)
                maxsel.update(sequpper)
        if mainlower - maxsel:
            return True
        return False

    def infer(self, dstore=None, verbosity=0, tracevar=[]):
        seqvars = self.seqvars
        selvar = self.selvar
        mainvar = self.mainvar
        changed = set()
        state = Constraint.sleeping

        sel_infer = Selection.infer(self, dstore=dstore, verbosity=verbosity, tracevar=tracevar)
        if sel_infer:
            return sel_infer
        ## Some variable(s) determined
        # Selection variable
        if selvar.determined(dstore=dstore, verbosity=verbosity, constraint=self) is not False:
            # If the selection var is determined, check whether the indexed sequence vars
            # are also
            all_determined = True
            selval = selvar.get_value(dstore=dstore)
            selseqs = [seqvars[index] for index in selval if index < len(seqvars)]
            result = set()
            for seq in selseqs:
                if seq.determined(dstore=dstore, verbosity=verbosity, constraint=self) is not False:
#                    print('Determined {}'.format(seq))
                    result.update(seq.get_lower(dstore=dstore))
                else:
                    all_determined = False
            if all_determined:
                # If so, determine the main var
                if mainvar.determine(result, dstore=dstore,
                                     constraint=(verbosity>1 or mainvar in tracevar) and self):
                    changed.add(mainvar)
                state = Constraint.entailed
                if verbosity > 1 and changed:
                    print('  Variables {} changed'.format(changed))
                return state, changed
            # Also check whether the main var is determined, in which case the seq vars
            # can possibly be constrained
            if mainvar.determined(dstore=dstore, verbosity=verbosity, constraint=self) is not False:
                mainvalue = mainvar.get_value(dstore=dstore)
                # Remove any values from upper bounds that are not in main var
                for seq in selseqs:
                    seq_up = seq.get_upper(dstore=dstore)
                        # unused_up is everything in seq's upper bound that's not in mainvalue
                    unused_up = seq_up - mainvalue
                    if unused_up:
#                        print("seqvar {}: seq_up {}, unused_up {}".format(seq, seq_up, unused_up))
                        if len(seq_up - unused_up) < seq.get_lower_card(dstore=dstore):
                            if verbosity:
                                if seq in tracevar:
                                    s = '  {} attempting to discard {} from upper bound of {}, making it too small'
                                    print(s.format(self, unused_up, seq))
                                print('{} failed'.format(self))
#                            print(self, 'failed because of attempt to make upper bound too small')
                            return Constraint.failed, set()
                        if seq.discard_upper(unused_up, dstore=dstore,
                                             constraint=(verbosity>1 or seq in tracevar) and self):
#                            if tracevar==seq:
#                                print(self, 'discarding', unused_up, 'from', seq, 'mainvalue', mainvalue, 'seq_up', seq_up)
                            changed.add(seq)
                            return state, changed
            # Even if seqvars are not determined, we may be able to constrain mainvar (as long as it's not
            # already determined)
            else:
                main_lowcard = max([seq.get_lower_card(dstore=dstore) for seq in selseqs])
                if mainvar.strengthen_lower_card(main_lowcard, dstore=dstore,
                                                 constraint=(verbosity>1 or mainvar in tracevar) and self):
                    changed.add(mainvar)
                    return state, changed
                seq_uppers = [seq.get_upper(dstore=dstore) for seq in selseqs]
                seq_up_union = set().union(*seq_uppers)
                if mainvar.strengthen_upper(seq_up_union, dstore=dstore,
                                            reduce=True,
                                            constraint=(verbosity>1 or mainvar in tracevar) and self):
                    changed.add(mainvar)
                    return state, changed
                if mainvar.strengthen_upper_card(len(seq_up_union), dstore=dstore,
                                                 constraint=(verbosity>1 or mainvar in tracevar) and self):
                    changed.add(mainvar)
                    return state, changed
                seq_lowers = [seq.get_lower(dstore=dstore) for seq in selseqs]
                if mainvar.strengthen_lower(set().union(*seq_lowers), dstore=dstore,
                                            constraint=(verbosity>1 or mainvar in tracevar) and self):
#                    s = "Strengthening lower bound of mainvar {}; seq lowers {}, seq uppers {}, main upper {}"
#                    print(s.format(mainvar, seq_lowers, seq_uppers, mainvar.get_upper(dstore=dstore)))
#                    if tracevar in selseqs:
#                        print(self, 'strengthening lower main 1', seq_lowers, seq_uppers, mainvar.get_upper(dstore=dstore),
#                              mainvar.get_upper_card(dstore=dstore))
                    changed.add(mainvar)
                    return state, changed

        # Main variable determined
        if mainvar.determined(dstore=dstore, verbosity=verbosity, constraint=self) is False:
            # The main variable must be a subset of the union of the upper bounds of all
            # sequence variables indexed by the upper bound of the selection variable.
            selupper = selvar.get_upper(dstore=dstore)
            for j in selupper:
                if j >= len(seqvars):
                    print(self, 'seqvars', seqvars, 'too short for', selupper, 'of variable', selvar)
            seq_uppers = [seqvars[j].get_upper(dstore=dstore) for j in selupper if j < len(seqvars)]
            if mainvar.strengthen_upper(set().union(*seq_uppers), dstore=dstore,
                                        reduce=True,
                                        constraint=(verbosity>1 or mainvar in tracevar) and self):
                changed.add(mainvar)
                return state, changed
            # The main variable must be a superset of the union of the lower bounds of all
            # sequence variables indexed by the lower bound of the selection variable.
            seq_lowers = [seqvars[j].get_lower(dstore=dstore) for j in selvar.get_lower(dstore=dstore)]
            if mainvar.strengthen_lower(set().union(*seq_lowers), dstore=dstore,
                                        constraint=(verbosity>1 or mainvar in tracevar) and self):
                changed.add(mainvar)
                return state, changed
        ## Neither selection variable nor main variable determined
        # If the lower bound of some seqvar is not a subset of mainvar's upperbound,
        # then exclude its index from selection var (remove it from the selection var's
        # upper bound)
        for j in selvar.get_upper(dstore=dstore).copy():
            # Consider only indices for seq vars that are in the upper bound of selection variable
            if j >= len(seqvars):
                continue
            seqvar = seqvars[j]
            seqlower = seqvar.get_lower(dstore=dstore)
            mainupper = mainvar.get_upper(dstore=dstore)
            if not seqlower <= mainupper:
                # If pattern is True and seqlower and mainupper unify, it's still OK
                # This should fail if by discarding j, the cardinality of upper has gone below lower card
                if len(selvar.get_upper(dstore=dstore) - {j}) < selvar.get_lower_card(dstore=dstore):
                    if verbosity:
                        if selvar in tracevar:
                            s = '  {} attempting to discard {} from upper bound of {}, making it too small'
                            print(s.format(self, j, selvar))
                        print('{} failed'.format(self))
                    return Constraint.failed, set()
                if selvar.discard_upper(j, dstore=dstore, constraint=(verbosity>1 or selvar in tracevar) and self):
                    changed.add(selvar)
                    return state, changed
        # If excluding any index from selection var's upper bound in figuring the
        # union of upper bounds of indexed sequence variables causes the lower bound
        # of the main variable to contain elements not in the union,
        # then add those elements to the excluded sequence
        # variable and the excluded index to the selection variable's lower bound
        selvar_upper = selvar.get_upper(dstore=dstore)
        for j in selvar_upper:
            if j >= len(seqvars):
                continue
            # Consider only indices in the upper bound of selection variable
            # Exclude j
            indices = selvar_upper - {j}
            # Get the union of the upper bounds of the indexed sequence variables
            seqvar_union = set().union(*[seqvars[i].get_upper(dstore=dstore) for i in indices if i < len(seqvars)])
            # Does the lower bound of the main variable have any elements not in the union?
            main_union_diff = mainvar.get_lower(dstore=dstore) - seqvar_union
            if len(main_union_diff) > 0:
#                print(self, 'excluding index', j, 'indices', indices, 'seqvar_union',
#                      seqvar_union, 'main_union_diff', main_union_diff)
#                print('  Attempting to strengthen lower bound of', seqvars[j])
                # Yes; add the difference to the excluded seq var's lower bound
                if seqvars[j].strengthen_lower(main_union_diff, dstore=dstore,
                                               constraint=(verbosity>1 or seqvars[j] in tracevar) and self):
                    changed.add(seqvars[j])
#                    s = 'Strengthening lower of seqvar {}, main union diff {}'
#                    print(s.format(seqvars[j], main_union_diff))
                    return state, changed
                # and add the index to selection var's lower bound
                if selvar.strengthen_lower({j}, dstore=dstore,
                                           constraint=(verbosity>1 or selvar in tracevar) and self):
                    changed.add(selvar)
                    return state, changed
        # For all seq vars in the lower bound of selvar, exclude any elements that are not in the
        # upper bound of mainvar (not in Duchier??)
        selvar_lower = selvar.get_lower(dstore=dstore)
        mainvar_upper = mainvar.get_upper(dstore=dstore)
        seqvar_upper = set().union(*[seqvars[i].get_upper(dstore=dstore) for i in selvar_lower if i < len(seqvars)])
        seq_main_diff = seqvar_upper - mainvar_upper
        if seq_main_diff:
            for j in selvar_lower:
                if j >= len(seqvars):
                    continue
                seq = seqvars[j]
#                if seq in tracevar:
                if len(seqvar_upper - seq_main_diff) < seq.get_lower_card(dstore=dstore):
                    if verbosity:
                        if seq in tracevar:
                            s = '  {} attempting to discard {} from upper bound of {}, making it too small'
                            print(s.format(self, unused_up, seq))
                        print('{} failed'.format(self))
                    return Constraint.failed, set()
                elif seq.discard_upper(seq_main_diff, dstore=dstore, constraint=(verbosity>1 or seq in tracevar) and self):
#                    print(self, 'discarding', seq_main_diff, 'from', seq,
#                          'mainvar_upper', mainvar_upper,
#                          'seqvar_upper', seqvar_upper,
#                          'selvar_lower', selvar_lower)
                    changed.add(seq)
                    return state, changed

        if verbosity > 1 and changed:
            print('  Variables {} changed'.format(changed))
        return state, changed

class IntersectionSelection(Selection):
    '''All variables are set vars. Select the intersection of the selected sets.'''

    def __init__(self, mainvar=None, selvar=None, seqvars=None, problem=None, weight=1,
                 record=True):
        Selection.__init__(self, mainvar=mainvar, selvar=selvar, seqvars=seqvars,
                           problem=problem, weight=weight, record=record)
        self.name = '{0} = ^{1} [{2}]'.format(self.mainvar, self.format_seq(self.seqvars), self.selvar)

    def sel_upper(self, dstore=None):
        """Upper bound on values that *can* be selected."""
        seq_len = len(self.seqvars)
        selvar_lower = self.selvar.get_lower(dstore=dstore)
        if not selvar_lower:
            # There's nothing we can say about what must be selected
            return True
        if any([i >= seq_len for i in selvar_lower]):
            return False
        selvar_lower = list(selvar_lower)
        res = self.seqvars[selvar_lower[0]].get_upper(dstore=dstore)
        for i in selvar_lower[1:]:
            res = res & self.seqvars[i].get_upper(dstore=dstore)
        return res

    def fails(self, dstore=None):
        """Fail if the lower bound of sel var has indices beyond the length of seq vars
        or if the lower bound of mainvar is a superset of the values that can be included."""
        sel_upper = self.sel_upper(dstore=dstore)
        if sel_upper is False:
#            print('Failed because sel_upper', sel_upper, 'is False')
            return True
        if sel_upper is True:
            return False
        if sel_upper < self.mainvar.get_lower(dstore=dstore):
            # Lower bound of mainvar includes values that can't be selected
#            print('Failed because sel_upper', sel_upper, 'is less than main lower', self.mainvar.get_lower(dstore=dstore))
            return True
        return False

    def infer(self, dstore=None, verbosity=0, tracevar=None):
        seqvars = self.seqvars
        selvar = self.selvar
        mainvar = self.mainvar
        changed = set()
        state = Constraint.sleeping

        sel_infer = Selection.infer(self, dstore=dstore, verbosity=verbosity, tracevar=tracevar)
        if sel_infer:
            return sel_infer

        if selvar.determined(dstore=dstore, verbosity=verbosity, constraint=self) is not False:
            # If the selection var is determined, check whether the indexed sequence vars
            # are also
            all_determined = True
            selval = selvar.get_value(dstore=dstore)
            to_intersect = []
            for index in selval:
                seq = seqvars[index]
                if seq.determined(dstore=dstore, verbosity=verbosity, constraint=self) is not False:
                    # Intersect result with lower bound of seq
                    to_intersect.append(seq.get_lower(dstore=dstore))
                else:
                    all_determined = False
            if all_determined:
                # Intersect the sets found in lower bounds
                if to_intersect:
                    inters = to_intersect[0].intersection(*to_intersect[1:])
                else:
                    inters = set()
                # If so, determine the main var using the accumulated intersection
                if mainvar.determine(inters, dstore=dstore, constraint=(verbosity>1 or mainvar in tracevar) and self):
                    changed.add(mainvar)
                state = Constraint.entailed
                if verbosity > 1 and changed:
                    print('  Variables {} changed'.format(changed))
                return state, changed
            # Also check whether the main var is determined, in which case the seq vars
            # can possibly be constrained
            if mainvar.determined(dstore=dstore, verbosity=verbosity, constraint=self) is not False:
                mainvalue = mainvar.get_value(dstore=dstore)
                # Selected seq vars
                selseqs = [seqvars[i] for i in selval]
                # Lower bounds of selected seq vars
                seqlower = list([seq.get_lower(dstore=dstore) for seq in selseqs])
                # Upper bounds of selected seq vars
                sequpper = [seq.get_upper(dstore=dstore) for seq in selseqs]
                # Intersection of lower bounds
                seqinters = seqlower[0].intersection(*seqlower[1:])
                # Unaccounted for elements in main value; these have to appear in all seq vars
                unaccounted = mainvalue - seqinters
                for seq in selseqs:
                    if seq.strengthen_lower(unaccounted, dstore=dstore,
                                            constraint=(verbosity>1 or seq in tracevar) and self):
                        changed.add(seq)

        # The main variable must be a superset of the intersection of the lower bounds of all
        # sequence variables indexed by the upper bound of the selection variable.
        seq_lowers = list([seqvars[j].get_lower(dstore=dstore) for j in selvar.get_upper(dstore=dstore)])
        if mainvar.strengthen_lower(seq_lowers[0].intersection(*seq_lowers[1:]), dstore=dstore,
                                    constraint=(verbosity>1 or mainvar in tracevar) and self):
            changed.add(mainvar)
        sellower = selvar.get_lower(dstore=dstore)
        if len(sellower) > 0:
            # The main variable must be a subset of the intersection of the upper bounds of all
            # sequence variables indexed by the lower bound of the selection variable.
            seq_uppers = list([seqvars[j].get_upper(dstore=dstore) for j in sellower])
            if mainvar.strengthen_upper(seq_uppers[0].intersection(*seq_uppers[1:]), dstore=dstore,
                                        constraint=(verbosity>1 or mainvar in tracevar) and self):
                changed.add(mainvar)
        # If the upper bound of some seqvar is not a superset of mainvar's lower bound,
        # then exclude its index from selection var (remove it from the selection var's
        # upper bound)
        for j in selvar.get_upper(dstore=dstore).copy():
            # Consider only indices that are in the upper bound of selection variable
            seqvar = seqvars[j]
            if not seqvar.get_upper(dstore=dstore) >= mainvar.get_lower(dstore=dstore):
                if selvar.discard_upper(j, dstore=dstore, constraint=(verbosity>1 or selvar in tracevar) and self):
                    changed.add(selvar)
        # If excluding any index from selection var's LOWER bound in figuring the
        # INTERSECTION of LOWER bounds of indexed sequence variables causes INTERSECTION to
        # contain elements not in the UPPER bound of the main variable,
        # then EXCLUDE those elements from the upper bound of the excluded seq var
        # and add the excluded index to the selection variable's lower bound
        for j in sellower:
            # Consider only indices that in the lower bound of selection variable
            # Exclude j
            indices = sellower - {j}
            # Get the intersection of the lower bounds of the indexed sequence variables
            seq_lowers = list([seqvars[i].get_lower(dstore=dstore) for i in indices])
            if not seq_lowers:
                continue
            seqvar_inters = seq_lowers[0].intersection(*seq_lowers[1:])
            # Does this intersection have any values not in the upper bound of the main var
            inters_main_diff = seqvar_inters - mainvar.get_upper(dstore=dstore)
            if len(inters_main_diff) > 0:
                # Yes; exclude the values in the intersection from the excluded seq var's upper bound
                for val in inters_main_diff:
                    if seqvars[j].discard_upper(val, dstore=dstore,
                                                constraint=(verbosity>1 or seqvars[j] in tracevar) and self):
                        changed.add(seqvars[j])
                # and add the index to selection var's lower bound
                if selvar.strengthen_lower({j}, dstore=dstore, constraint=(verbosity>1 or selvar in tracevar) and self):
                    changed.add(selvar)
        if verbosity > 1 and changed:
            print('  Variables {} changed'.format(changed))
        return state, changed

class AgrSelection(Constraint):
    """Selection variable is a determined set of tuples of 3 or more elements:
    (index1, index2, (feat1, feat2), ...)
    where (feat1, feat2) means feat1 for the element with index1 must agree with
    feat2 for the element with index2 (indices in index space 1).
    Each of the sequence variables maps indices in the selection variable (index space 1)
    onto another set of indices (index space 2 'snode' variable for each gnode in Mbojereha).
    Each of the feature variables is a list of features objects or dicts associated
    with an element in index space 2.
    """

    def __init__(self, featvars=None, selvar=None, seqvars=None,
                 problem=None, weight=1, record=True):
        Constraint.__init__(self, featvars + [selvar] + seqvars, problem=problem,
                            weight=weight, record=record)
        self.featvars = featvars
        self.selvar = selvar
        self.seqvars = seqvars
        self.name = '[{0}] = <{1}> {2}'.format(self.featvars, self.seqvars, AgrSelection.selvar_string(selvar.get_value()))

    @staticmethod
    def selvar_string(value):
        constraints = []
        for attribs in value:
            s = "{{({},{}):".format(attribs[0], attribs[1])
            agrs = []
            for f1, f2 in attribs[2:]:
                agrs.append("{}={}".format(f1, f2))
            s += ','.join(agrs) + "}"
            constraints.append(s)
        return '[' + ';'.join(constraints) + ']'

    def fail_featvars(self, fv0, fv1, agr, dstore=None):
        """Do feat vars fv0 and fv1 fail to satisfy agr constraints?"""
        fv0upper = fv0.get_upper(dstore=dstore)
        fv1upper = fv1.get_upper(dstore=dstore)
        fv0lowcard = fv0.get_lower_card(dstore=dstore)
        fv1lowcard = fv1.get_lower_card(dstore=dstore)
        n_agr0, n_agr1 = FeatStruct.n_agree(fv0upper, fv1upper, agr)
        return n_agr0 < fv0lowcard or n_agr1 < fv1lowcard

    def fails(self, dstore=None):
        """Fail if any combinations in the lower bounds of any pairs of seqvars indexed
        in selvar index pairs of featvars which don't have enough agreeing features in their
        upper bounds."""
        for attribs in self.selvar.get_lower(dstore=dstore):
            i0, i1, agr = attribs[0], attribs[1], attribs[2:]
            seq0, seq1 = self.seqvars[i0], self.seqvars[i1]
            seq0lower = seq0.get_lower(dstore=dstore)
            seq1lower = seq1.get_lower(dstore=dstore)
            for s0 in seq0lower:
                for s1 in seq1lower:
                    fv0, fv1 = self.featvars[s0], self.featvars[s1]
                    if self.fail_featvars(fv0, fv1, agr, dstore=dstore):
                        return True
        return False

    def is_entailed(self, dstore=None):
        """Entailed if all combinations in the upper bounds of seqvars indexed in
        in selvar index pairs of featvars whose upper bounds agree on the relevant
        features."""
        for attribs in self.selvar.get_upper(dstore=dstore):
            i0, i1, agr = attribs[0], attribs[1], attribs[2:]
            seq0, seq1 = self.seqvars[i0], self.seqvars[i1]
            seq0upper = seq0.get_upper(dstore=dstore)
            seq1upper = seq1.get_upper(dstore=dstore)
            for s0 in seq0upper:
                for s1 in seq1upper:
                    feat0, feat1 = self.featvars[s0], self.featvars[s1]
                    for f0 in feat0.get_upper(dstore=dstore):
                        for f1 in feat1.get_upper(dstore=dstore):
                            if not f0.agrees(f1, agr):
                                return False
        return True


    def infer(self, dstore=None, verbosity=0, tracevar=[]):
        """Remove feats from featvars if they have to agree because of lower bound
        of seqvars. Remove indices from seqvars if the indexed featvars can't agree."""
        """Fail if any combinations in the lower bounds of any pairs of seqvars indexed
        in selvar index pairs of featvars whose lower bounds fail to agree on the relevant
        features."""
        changed = set()
        state = Constraint.sleeping
        for attribs in self.selvar.get_lower(dstore=dstore):
            # Try to eliminate features from upper bounds of featvars
            # THERE IS A MUCH MORE EFFICIENT WAY TO DO THIS
            i0, i1, agr = attribs[0], attribs[1], attribs[2:]
            seq0, seq1 = self.seqvars[i0], self.seqvars[i1]
            seq0lower = seq0.get_lower(dstore=dstore)
            seq1lower = seq1.get_lower(dstore=dstore)
            for s0 in seq0lower:
                for s1 in seq1lower:
                    feat0, feat1 = self.featvars[s0], self.featvars[s1]
                    feat0undec = feat0.get_undecided(dstore=dstore)
                    feat1lower = feat1.get_lower(dstore=dstore)
                    failfeat0 = FeatStruct.agree_with_none1(feat0undec, feat1lower, agr)
                    if failfeat0:
                        if feat0.discard_upper(failfeat0, dstore=dstore,
                                               constraint=(verbosity>1 or feat0 in tracevar) and self):
                            changed.add(feat0)
                            return state, changed
                    feat1undec = feat1.get_undecided(dstore=dstore)
                    feat0lower = feat0.get_lower(dstore=dstore)
                    failfeat1 = FeatStruct.agree_with_none2(feat0lower, feat1undec, agr)
                    if failfeat1:
                        if feat1.discard_upper(failfeat1, dstore=dstore,
                                               constraint=(verbosity>1 or feat1 in tracevar) and self):
                            changed.add(feat1)
                            return state, changed
            # Try to eliminate indices from upper bounds of seqvars
            seq0upper = seq0.get_undecided(dstore=dstore)
            seq1lower = seq1.get_lower(dstore=dstore)
            for s0 in seq0upper:
                for s1 in seq1lower:
                    feat0, feat1 = self.featvars[s0], self.featvars[s1]
                    if self.fail_featvars(feat0, feat1, agr, dstore=dstore):
                        if seq0.discard_upper(s0, dstore=dstore,
                                              constraint=(verbosity>1 or feat0 in tracevar) and self):
                            changed.add(seq0)
                            return state, changed
            seq0lower = seq0.get_lower(dstore=dstore)
            seq1upper = seq1.get_undecided(dstore=dstore)
            for s0 in seq0lower:
                for s1 in seq1upper:
                    feat0, feat1 = self.featvars[s0], self.featvars[s1]
                    if self.fail_featvars(feat0, feat1, agr, dstore=dstore):
#                    for f0 in feat0.get_lower(dstore=dstore):
#                        for f1 in feat1.get_lower(dstore=dstore):
#                            if not f0.agrees(f1, agr):
                        if seq1.discard_upper(s1, dstore=dstore,
                                              constraint=(verbosity>1 or feat0 in tracevar) and self):
                            changed.add(seq1)
                            return state, changed
        return state, changed

class PrecedenceSelection(Constraint):
    """
    PrecedenceSelection is different enough from UnionSelection and IntersectionSelection
    to not inherit from the Selection class.

    posvars: set vars consisting of int positions (determined for analysis, not for generation)
    selvar: a set var consisting of pairs of indices within posvars, each
    pair specifying a precedence constraint between the corresponding sets
    """

    def __init__(self, selvar=None, posvars=None, problem=None,
                 weight=1, maxset=None, record=True):
        Constraint.__init__(self, [selvar] + posvars, problem=problem,
                            weight=weight, record=record)
        self.selvar = selvar
        self.posvars = posvars
        # Maximum set of tuples for the particular problem (normally depends on number of arc
        # labels for LP dimension)
        self.maxset = maxset or ALL
        self.name = '<< {} [{}]'.format(Selection.format_seq(self.posvars), self.selvar)

    def is_entailed(self, dstore=None):
        """Entailed if all variables are determined or
        if all pairs of indices that *could* be included correspond to
        constraints that are already satisfied.
        """
        if self.selvar.determined(dstore=dstore, constraint=self) is not False \
           and all([v.determined(dstore=dstore, constraint=self) is not False for v in self.posvars]):
            return True
        selupper = self.selvar.get_upper(dstore=dstore)
        for first, second in selupper:
            var1 = self.posvars[first]
            var2 = self.posvars[second]
            if not SetPrecedence.must_precede(var1, var2, dstore=dstore):
                return False
        return True

    def fails(self, dstore=None):
        """Fail if the lower bound of selvar includes pairs representing variables
        that necessarily violate the precedence constraint."""
        sellower = self.selvar.get_lower(dstore=dstore)
        for first, second in sellower:
            # elements in first variable must precede those in second
            # as in SetPrecedence
            var1 = self.posvars[first]
            var2 = self.posvars[second]
            if SetPrecedence.cant_precede(var1, var2, dstore=dstore):
                return True
        return False

    def infer(self, dstore=None, verbosity=0, tracevar=[]):
        changed = set()
        state = Constraint.sleeping

        ## Constrain the selection variable based on the position variables.
        # For each pair of indices in the sel var's upper bound, check to see
        # whether the corresponding precedence constraint can't succeed
        discard_selup = set()
        strengthen_sellow = set()
        for first, second in self.selvar.get_upper(dstore=dstore):
            var1 = self.posvars[first]
            var2 = self.posvars[second]
            if SetPrecedence.cant_precede(var1, var2, dstore=dstore):
                discard_selup.add((first, second))
        if discard_selup:
            if self.selvar.discard_upper(discard_selup, dstore=dstore,
                                         constraint=(verbosity>1 or self.selvar in tracevar) and self):
                changed.add(self.selvar)
                return state, changed

        ## Constrain the position variables based on the selection variable.
        # For each pair of indices in the sel var's lower bound, check to see
        # whether indices can be excluded from the upper bounds of the corresponding
        # position variables.
        for first, second in self.selvar.get_lower(dstore=dstore):
            v1 = self.posvars[first]
            v2 = self.posvars[second]
            v1_low = v1.get_lower(dstore=dstore)
            v2_low = v2.get_lower(dstore=dstore)
            v1_up = v1.get_upper(dstore=dstore)
            v2_up = v2.get_upper(dstore=dstore)
            # If the lower bound on v1 is not empty, v2 must be a subset of
            # {min(MAX, max(v1 + 1)), ..., MAX}
            if v1_low and v1_up and v2_up:
                v2_up_new = range(min([max(v1_up), max(v1_low) + 1]), max(v2_up)+1)
                if v2.strengthen_upper(v2_up_new, dstore=dstore,
                                       constraint=(verbosity>1 or v2 in tracevar) and self):
                    changed.add(v2)
#                    print('1 Strengthened', v2)
                    return state, changed
            # If the lower bound on v2 is not empty, v1 must be a subset of
            # {0, ..., max(0, min(v2_low) - 1)}
            if v2_low:
                v1_up_new = range(0, max([0, min(v2_low) - 1]) + 1)
                if v1.strengthen_upper(v1_up_new, dstore=dstore,
                                       constraint=(verbosity>1 or v1 in tracevar) and self):
                    changed.add(v1)
#                    print('2 Strengthened', v1)
                    return state, changed
            v1_up = v1.get_upper(dstore=dstore)
            v2_up = v2.get_upper(dstore=dstore)
#            if verbosity>1 or v1 in tracevar:
#                print('v1', v1, 'v2', v2,
#                      'v1_up', v1_up, 'v2_up', v2_up,
#                      'v1_lc', v1.get_lower_card(dstore=dstore),
#                      'v2_lc', v2.get_lower_card(dstore=dstore))
            if v1_up and v2_up and v1.get_lower_card(dstore=dstore) and v2.get_lower_card(dstore=dstore):
                # Eliminate elements of v1 upper that are >= max of v2 upper
                lowenough1 = {x for x in v1_up if x < max(v2_up)}
                if v1.strengthen_upper(lowenough1, dstore=dstore,
                                       constraint=(verbosity>1 or v1 in tracevar) and self):
                    changed.add(v1)
#                    print('4 Strengthened', v1)
                    return state, changed
                # Eliminate elements of v2 upper that are <= min of v1 upper
                # (v1_up might have changed so assign again and check whether it's empty)
                v1_up = v1.get_upper(dstore=dstore)
                if v1_up:
                    highenough2 = {x for x in v2_up if x > min(v1_up)}
                    if v2.strengthen_upper(highenough2, dstore=dstore,
                                           constraint=(verbosity>1 or v2 in tracevar) and self):
#                        print('3 Strengthened', v2)
                        changed.add(v2)
                        return state, changed
        return state, changed

class DependencySelection(Constraint):
    """
    Like PrecedenceSelection, DependencySelection has only two variables so does not inherit
    from Selection.

    depvars: list of determined set vars
       for each position in depvars i, representing an element (for example, a GInst in Mbojereha),
       the set var consists of the positions in depvars for other elements that must be selected for
       if element i is to be selected for
    selvar: a set var consisting of positions (indices) in the depvars list, representing elements,
       for example, groups in Mbojereha
    """

    def __init__(self, selvar=None, depvars=None,
                 problem=None, weight=1, maxset=None, record=True):
        Constraint.__init__(self, [selvar] + depvars,
                            problem=problem, weight=weight, record=record)
        self.selvar = selvar
        self.depvars = depvars
        self.name = '--> {} [{}]'.format(Selection.format_seq(self.depvars), self.selvar)

    def is_entailed(self, dstore=None):
        """Entailed if the selvar is determined (the depvars already are) or if
        for all i in selvar.lower, either there are no depvars[i] or all depvars[i] are in selvar.lower.
        """
        if self.selvar.determined(dstore=dstore, constraint=self) is not False:
            return True
        sellower = self.selvar.get_lower(dstore=dstore)
        if not sellower:
            return False
        for seli in sellower:
            depvar = self.depvars[seli]
            depsi = depvar.get_value(dstore)
            if depsi and not depsi < sellower:
                return False
        return True

    def fails(self, dstore=None):
        """Fail if for any i in selvar.lower, none of depvars[i] is in selvar.upper."""
        sellower = self.selvar.get_lower(dstore=dstore)
        selupper = self.selvar.get_upper(dstore=dstore)
        for seli in sellower:
            depvar = self.depvars[seli]
            depsi = depvar.get_value(dstore)
            if depsi and not depsi & selupper:
                return True
        return False

    def infer(self, dstore=None, verbosity=0, tracevar=[]):
        changed = set()
        state = Constraint.sleeping
        sellower = self.selvar.get_lower(dstore=dstore)
        selupper = self.selvar.get_upper(dstore=dstore)

        for seli in selupper:
            # For all elements that CAN be selected
            # See if NONE of its dependents can be selected
            depvar = self.depvars[seli]
            depsi = depvar.get_value(dstore)
            if depsi and not depsi & selupper:
                # If so, discard seli from selvar.upper
                if self.selvar.discard_upper(seli, dstore=dstore,
                                             constraint=(verbosity>1 or self.selvar in tracevar) and self):
                    changed.add(self.selvar)
                    return state, changed

        for seli in sellower:
            # For all elements that MUST be selected
            # See if only one dependent is possible and not already in self.lower
            depvar = self.depvars[seli]
            depsi = depvar.get_value(dstore)
            if depsi:
                poss_depsi = depsi & selupper
                if len(poss_depsi) == 1:
                    if not poss_depsi < sellower:
                        # If so, this element must be selected (strengthen_lower for it)
                        if self.selvar.strengthen_lower(poss_depsi, dstore=dstore,
                                                        constraint=(verbosity>1 or self.selvar in tracevar) and self):
                            changed.add(self.selvar)
                            return state, changed

        return state, changed

### Complex selection constraints

class ComplexConstraint(Constraint):
    """Each value of selection variable (potentially) selects a simple constraint."""

    def __init__(self, selvar=None, selvars=None, othervars=None,
                 problem=None, weight=1, record=True):
        Constraint.__init__(self, [selvar] + selvars + othervars, problem=problem, weight=weight,
                            record=record)
        self.selvar = selvar
        self.selvars = selvars
        self.constraints = []

    def fails(self, dstore=None):
        """Fail if any of the constraints indexed by the lower bound of selvar fail."""
        for index in self.selvar.get_lower(dstore=dstore):
            constraint = self.constraints[index]
            if constraint and constraint.fails(dstore=dstore):
                print("-->>CC failed: {}, {}, {}".format(index, self.selvar.get_lower(dstore=dstore), constraint))
                return True
        return False

    def is_entailed(self, dstore=None):
        """Is entailed if all of the constraints indexed by the upper bound of selvar are entailed."""
        selvar_upper = self.selvar.get_upper(dstore=dstore)
        for index in selvar_upper:
            constraint = self.constraints[index]
            if constraint and not constraint.is_entailed(dstore=dstore):
                return False
        # Remove non-indexed selection variables from essential variable list
        # if they're there.
        for index, selvar in enumerate(self.selvars):
            if index not in selvar_upper:
                if selvar in dstore.ess_undet:
#                    print("Removing {} from DStore essential variables".format(selvar))
                    dstore.ess_undet.remove(selvar)
        return True

    def infer(self, dstore=None, verbosity=0, tracevar=[]):
        """Run infer() on all constraints indexed in the lower bound of selvar,
        and remove indices from the upper bound of selvar if the indexed constraint
        fails."""
        selvar = self.selvar
        selupper = selvar.get_upper(dstore=dstore)
        sellower = selvar.get_lower(dstore=dstore)
        for index, constraint in enumerate(self.constraints):
            if not constraint:
                continue
            if index in sellower:
                state, changed = constraint.infer(dstore=dstore)
                # If any variable changed as a result this, return it
                if changed:
                    return state, changed
            elif index in selupper:
                # A constraint indexed by a value in the upper bound of selvar failed
                if constraint.fails(dstore=dstore):
                    # Try to remove this index from the upper bound of selvar
                    if selvar.discard_upper(index, dstore=dstore,
                                            constraint=(verbosity>1 or selvar in tracevar) and self):
                        return Constraint.sleeping, {selvar}

        return Constraint.sleeping, set()

class ComplexUnionSelection(ComplexConstraint):
    """Each value of selection variable (potentially) selects a union selection constraint, with each of the
    selection variables (selvars) as the selection variable for one of these."""

    def __init__(self, selvar=None, mainvars=None, seqvars=None, selvars=None,
                 problem=None, weight=1, record=True):
        ComplexConstraint.__init__(self, selvar, selvars, seqvars + mainvars,
                                   problem=problem, weight=weight, record=record)
        self.seqvars = seqvars
        self.mainvars = mainvars
        self.name = '{} = U{} [{}] [[{}]]'.format(Selection.format_seq(mainvars),
                                                  Selection.format_seq(seqvars),
                                                  Selection.format_seq(selvars),
                                                  selvar)
        for sel, main in zip(selvars, mainvars):
            if not sel.get_upper():
                self.constraints.append(None)
            else:
                # Don't record this constraint in its variables
                self.constraints.append(UnionSelection(main, sel, seqvars,
                                                       record=False, weight=1, maxset=None))

class ComplexSetConvexity(ComplexConstraint):
    """Each value of selection variable (potentially) selects a set convexity constraint over one of
    the seqvars."""

    def __init__(self, selvar=None, convexvars=None, problem=None, weight=1, record=True):
        ComplexConstraint.__init__(self, selvar, selvars=convexvars, othervars=[],
                                   problem=problem, weight=weight, record=record)
        self.convexvars = convexvars
        self.name = '{} <> [{}]'.format(Selection.format_seq(self.convexvars), self.selvar)
        for cv in convexvars:
            # Don't record this constraint in the variables
            self.constraints.append(SetConvexity(cv, weight=weight, record=False))

class ComplexAgrSelection(ComplexConstraint):
    """Generalize AgrSelection to multiple values for the selection variables (selvars), which are selected by
    a meta-selection variable (selvar). Works similarly to ComplexUnionSelection."""

    def __init__(self, selvar=None, featvars=None, selvars=None, seqvars=None,
                 problem=None, weight=1, record=True):
        ComplexConstraint.__init__(self, selvar, selvars, seqvars + featvars,
                                   problem=problem, weight=weight, record=record)
        self.featvars = featvars
        self.selvars = selvars
        self.seqvars = seqvars
        self.name = '[{}] = <{}> [{}] [[{}]]'.format(featvars, seqvars,
                                                     ';;'.join([AgrSelection.selvar_string(v.get_value()) for v in selvars]),
                                                     selvar)
        for sel in selvars:
            # Each of the selvars is a determined set variable containing a set of triple+ constraints.
            if not sel.get_upper():
                # No constraint necessary for this selvar position
                self.constraints.append(None)
            else:
                # Create an AgrSelection constraint for this agr selection variable
                self.constraints.append(AgrSelection(featvars, sel, seqvars, record=False, weight=1))

### Constraints derived from other Constraints

class DerivedConstraint:
    """Abstract class for constraints that are equivalent to a conjunction of primitive or derived constraints."""

    def __init__(self, variables, problem=None, weight=1, record=True):
        self.variables = variables
        self.problem = problem
        self.weight = weight
        self.record = record
        self.init_constraints()

    def init_constraints(self):
        raise NotImplementedError("{} is an abstract class".format(self.__class__.__name__))

    def set_weight(self, weight):
        self.weight = weight
        for c in self.constraints:
            c.weight = weight

class Inclusion(DerivedConstraint):
    """Set inclusion:
    S1 c= S2: S1 c= S2 U S3 and S3 c= 0
    """

    def init_constraints(self):
        sv3 = EMPTY
        self.constraints = [SubsetUnion(self.variables + [sv3], problem=self.problem,
                                        weight=self.weight, record=self.record)]

class Disjoint(DerivedConstraint):
    """S1 || S2 || S3...: 0 >= S1 ^ S2 and 0 >= S1 ^ S3 and 0 >= S2 ^ S3...
    The variables must not share any elements.
    """

    def init_constraints(self):
        sv3 = EMPTY
        self.constraints = []
        for i, sv1 in enumerate(self.variables[:-1]):
            if sv1 == EMPTY:
                continue
            for sv2 in self.variables[i+1:]:
                if sv2 == EMPTY:
                    continue
                self.constraints.append(SupersetIntersection([sv3, sv1, sv2], problem=self.problem,
                                                             weight=self.weight, record=self.record))

# A dict of DetSVars for different values so these don't get recreated each time
# Union is instantiated
DetVarD = dict([(n, DetVar('sel' + str(n), set(range(n)))) for n in range(1, 20)])

class Union(DerivedConstraint):
    """S0 = S1 U S2 U ... :
    S0 = U<S1,...,Sn>[0,...n-1]."""

#    def __repr__():
#        ...

    def init_constraints(self):
        nvar = len(self.variables) - 1
        selvar = DetVarD.get(nvar) or DetVar('sel', set(range(nvar)))
        self.constraints = [UnionSelection(self.variables[0], selvar, self.variables[1:],
                                           problem=self.problem,
                                           weight=self.weight,
                                           record=self.record)]

class Intersection(DerivedConstraint):
    """S0 = S1 ^ S2 ^ ... :
    S0 = ^<S1,...,Sn>[0,...n-1]."""

    def init_constraints(self):
        nvar = len(self.variables) - 1
        selvar = DetVarD.get(nvar) or DetVar('sel', set(range(nvar)))
        self.constraints = [IntersectionSelection(self.variables[0], selvar, self.variables[1:],
                                                  problem=self.problem,
                                                  weight=self.weight,
                                                  record=self.record)]

class Partition(DerivedConstraint):
    """S0 = S1 U+ ... U+ Sn:
    S0 = S1 U ... U Sn and S1 || ... || Sn.
    The first variable is the union of the remaining variables, which must not share any elements.
    """

    def init_constraints(self):
        self.constraints = Union(self.variables, problem=self.problem, weight=self.weight, record=self.record).constraints
        self.constraints.extend(Disjoint(self.variables[1:], problem=self.problem, weight=self.weight, record=self.record).constraints)
