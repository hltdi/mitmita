#   
#   Mainumby variables and domain stores: required for constraint satisfaction.
#
########################################################################
#
#   This file is part of the HLTDI L^3 project
#   for parsing, generation, translation, and computer-assisted
#   human translation.
#
#   Copyright (C) 2014, 2015, 2016 PLoGS <gasser@indiana.edu>
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

# 2014.02.14
# -- Created. Copied from l3xdg/variable.py.
# 2014.03.26
# -- One variable class (SVar from l3xdg).
# 2014.05.04-5
# -- List variables; needed so they can include non-hashable elements,
#    in particular, dicts and Features objects: LVar, DetLVar

# Maximum number of values for a variable.
MAX = 200
# Maximum set of integers
ALL = set(range(MAX))

class DStore:
    """Domain store holding domains for variables. (Really the domains are held in
    dicts kept by the variables.)"""

    def __init__(self, name='', level=0, problem=None, parent=None):
        """This store is a strengthening of parent store if there is one."""
        self.problem = problem
        self.parent = parent
        self.children = []
        self.name = name
        self.level = level
        # Undetermined variables
        self.undetermined = []
        # Essential undetermined variables
        self.ess_undet = []

    def __repr__(self):
        return '@ {}/{}'.format(self.name, self.level)

    def is_determined(self, essential=True, verbosity=0):
        """Are all variables in dstore determined that need to be determined?"""
        if essential:
            if self.ess_undet:
                if verbosity:
                    print('{} has {} undetermined variables'.format(self, len(self.ess_undet)))
                return False
            else:
                return True
        elif self.undetermined:
            if verbosity:
                print('{} has {} undetermined variables'.format(self, len(self.undetermined)))
            return False
        return True
    
    def clone(self, constraint=None, name='', project=False, verbosity=0):
        """Create a new dstore by applying the basic constraint
        to the bindings in this store."""
        new_store = DStore(name=name or self.name, level=self.level+1,
                           problem=self.problem, parent=self)
        self.children.append(new_store)
        new_store.undetermined = self.undetermined[:]
        new_store.ess_undet = self.ess_undet[:]
        constraint.infer(dstore=new_store, verbosity=0, tracevar=[])
        for var in constraint.variables:
            # See if the new variable(?s) is now determined
            var.determined(dstore=new_store, verbosity=0)
        return new_store

DS0 = DStore(name='top')

class Var:

    # Threshold for "peripheral" variables
    weight_thresh = .5

    def __init__(self, name,
                 lower_domain=None, upper_domain=None,
                 lower_card=0, upper_card=MAX,
                 problem=None, dstores=None, rootDS=None,
                 constraint=None,
                 # Whether a complete solution depends on a single value for this variable
                 essential=True,
                 # Vars with low weights are "peripheral".
                 weight=1):
        self.name = name
        self.problem = problem
#        if problem:
#            self.problem.add_variable(self)
        self.constraints = [constraint] if constraint else []
        self.essential = essential
        self.value = None
        # Normally initialize with a top-level domain store
        self.rootDS = rootDS or DS0
        # Values of this variable in different domain stores
        self.dstores = dstores or {self.rootDS: {}}
        # Add the variable to the list of undetermined variables for
        # the dstore
        self.rootDS.undetermined.append(self)
        if essential:
            self.rootDS.ess_undet.append(self)
        self.weight = weight
        if lower_domain != None:
            self.lower_domain = lower_domain
        else:
            self.lower_domain = set()
        if upper_domain != None:
            self.upper_domain = upper_domain
        else:
            self.upper_domain = ALL.copy()
        self.init_lower_card = max(lower_card, len(self.lower_domain))
        self.init_upper_card = min(upper_card, len(self.upper_domain))
        self.max = MAX
        self.init_values(dstore=self.rootDS)

    def __repr__(self):
        return '${}'.format(self.name)

    # Initializing bounds

    def init_values(self, dstore=None):
        self.set_lower(self.lower_domain, dstore=dstore)
        self.set_upper(self.upper_domain, dstore=dstore)
        self.set_lower_card(self.init_lower_card, dstore=dstore)
        self.set_upper_card(self.init_upper_card, dstore=dstore)
        self.set_value(None, dstore=dstore)

    def set_lower(self, lower, dstore=None):
        self.set(dstore, 'lower', lower)

    def set_upper(self, upper, dstore=None):
        self.set(dstore, 'upper', upper)

    def set_lower_card(self, lower_card, dstore=None):
        self.set(dstore, 'lower_card', lower_card)

    def set_upper_card(self, upper_card, dstore=None):
        self.set(dstore, 'upper_card', upper_card)

    def get_name(self):
        '''Function used in sorting lists of variables.'''
        return self.name

    def get_dstore(self, dstore):
        """Returns the dictionary of value and domain(s) for dstore."""
        dstore = dstore or self.rootDS
        return self.dstores.get(dstore, {})

    def add_dstore(self, dstore):
        """Adds a domain store to the dstores dict."""
        self.dstores[dstore] = {}

    def set(self, dstore, feature, value):
        """Sets feature to be value in dstore, creating a dict for dstore if one doesn't exist."""
        dstore = dstore or self.rootDS
        dsdict = self.dstores.get(dstore, None)
        if dsdict == None:
            dsdict = {'value': None}
            self.dstores[dstore] = dsdict
        dsdict[feature] = value

    def set_value(self, value, dstore=None):
        """Sets the value of the variable in dstore."""
        self.set(dstore, 'value', value)

    def is_determined(self, dstore=None):
        """Is the variable already determined?"""
        return self.get_value(dstore=dstore) is not None

    def all_equal(self, variables, dstore=None):
        """Do all of these variables have the same value as this in dstore?"""
        return all([self.equals(var, dstore=dstore) for var in variables])

    def equals(self, var, dstore=None):
        """Does this variable have the same value as var in dstore?
        """
        value = self.get_value(dstore=dstore)
        if value != None:
            var_val = var.get_value(dstore=dstore)
            if var_val == None:
                return False
            if var.get_lower_card(dstore=dstore) > 1:
                return False
            if value == var_val:
                return True
        return False
        
    ## How constraints on a variable can fail

    def bound_fail(self, dstore=None):
        """Fail if the lower bound includes any elements not in the upper bound."""
        return self.get_lower(dstore=dstore) - self.get_upper(dstore=dstore)

    def card_fail(self, dstore=None):
        """Fail if the lower cardinality bound is greater than the upper cardinality bound."""
        return self.get_lower_card(dstore=dstore) > self.get_upper_card(dstore=dstore)

    def upper_bound_card_fail(self, dstore=None):
         """Fail if the length of upper bound < lower card."""
         return len(self.get_upper(dstore=dstore)) < self.get_lower_card(dstore=dstore)

    def lower_bound_card_fail(self, dstore=None):
        """Fail if length of lower bound > upper card."""
        return len(self.get_lower(dstore=dstore)) > self.get_upper_card(dstore=dstore)
        
    def fail(self, dstore=None):
        """Fail in one of three ways."""
        return self.bound_fail(dstore=dstore) or self.card_fail(dstore=dstore)
#            or self.bound_card_fail(dstore=dstore)

    ## Getters

    def get(self, dstore, feature, default=None):
        """Returns a value for feature associated with dstore, recursively
        checking dstore's parent is nothing is found."""
        dstore_dict = self.dstores.get(dstore, {})
        x = dstore_dict.get(feature, None)
        if x != None:
            return x
        parent = dstore.parent
        if parent:
            return self.get(parent, feature, default=default)
        return default

    def get_value(self, dstore=None):
        """Return the value of the variable in dstore."""
        dstore = dstore or self.rootDS
        return self.get(dstore, 'value', None)

    def get_lower(self, dstore=None):
        dstore = dstore or self.rootDS
        return self.get(dstore, 'lower')

    def get_upper(self, dstore=None):
        dstore = dstore or self.rootDS
        return self.get(dstore, 'upper')

    def get_lower_card(self, dstore=None):
        dstore = dstore or self.rootDS
        return self.get(dstore, 'lower_card', 0)

    def get_upper_card(self, dstore=None):
        dstore = dstore or self.rootDS
        return self.get(dstore, 'upper_card', MAX)

    def get_undecided(self, dstore=None):
        """Returns the set of values that may or may not be in the variable."""
        dstore = dstore or self.rootDS
        return self.get_upper(dstore=dstore) - self.get_lower(dstore=dstore)

    def det_update(self, dstore=None):
        if dstore:
            dstore.undetermined.remove(self)
            if self.essential:
                if self not in dstore.ess_undet:
                    print("Variable {} not in undetermined essentials: {}".format(self, dstore.ess_undet))
                    return
                dstore.ess_undet.remove(self)

    def determined(self, dstore=None, constraint=None, verbosity=0):
        """Attempt to determine the variable, returning the value if this is possible,
        False if it's not."""
        if verbosity > 1:
            print("Attempting to determine {} in {}".format(self, dstore))
        val = self.get_value(dstore=dstore)
        if val != None:
            if verbosity > 1:
                print("{} is already determined".format(self))
            return val
        def determined_help(value, dst, verb):
            value_card = len(value)
            lower_card = self.get_lower_card(dstore=dst)
            upper_card = self.get_upper_card(dstore=dst)
            if value_card < lower_card:
                s = "{} lowering lower card for {} to {}, less than previous value {}"
                raise(VarError(s.format(constraint, self, value_card, lower_card)))
            if value_card > upper_card:
                s = "{} raising upper card for {} to {}, greater than previous value {}"
                raise(VarError(s.format(constraint, self, value_card, upper_card)))
            self.set_value(value, dstore=dst)
            self.set_lower(value, dstore=dst)
            self.set_upper(value, dstore=dst)
            self.set_lower_card(value_card, dstore=dst)
            self.set_upper_card(value_card, dstore=dst)
            if verb > 1:
                print('  {} is determined at {}'.format(self, value))
            self.det_update(dstore=dst)
            return value
        lower = self.get_lower(dstore=dstore)
        upper = self.get_upper(dstore=dstore)
        if lower == None or upper == None:
            if verbosity > 1:
                print("  Failed to determine because upper or lower bound is None")
            return False
        # If upper and lower bounds are equal, determine at either
        if lower == upper:
            return determined_help(lower, dstore, verbosity)
        # Combine cardinality and set bounds to determine
        # If the length of the upper bound is <= the lower cardinality bound,
        # then make the upper bound the value
        if len(upper) <= self.get_lower_card(dstore=dstore):
            return determined_help(upper, dstore, verbosity)
        if len(lower) >= self.get_upper_card(dstore=dstore):
            return determined_help(lower, dstore, verbosity)
        if verbosity > 1:
            print("  Failed to determine, upper {}, lower {}".format(self.get_upper(dstore=dstore), self.get_lower(dstore=dstore)))
        return False

    ## Methods that can change the variable's set bounds or cardinality bounds
        
    def determine(self, value, dstore=None, constraint=None):
        """Attempt to determine the variable as value, returning False it can't be
        or if it's already determined."""
        if self.is_determined(dstore=dstore):
            return False
        value = value if isinstance(value, set) else {value}
        orig_upper = self.get_upper(dstore=dstore)
        orig_lower = self.get_lower(dstore=dstore)
        upper = self.get_upper(dstore=dstore)
        if not value.issubset(orig_upper):
            # Var can't be determined at this value
            return False
        if constraint:
            print('  {} determining {} as {}'.format(constraint, self, value))
        val_card = len(value)
        self.set_lower(value, dstore=dstore)
        self.set_upper(value, dstore=dstore)
        self.set_value(value, dstore=dstore)
        self.set_lower_card(val_card, dstore=dstore)
        self.set_upper_card(val_card, dstore=dstore)
        if dstore and self in dstore.undetermined:
            self.det_update(dstore)
        if orig_upper != value or orig_lower != value:
            return True
        return False

    def strengthen_upper(self, upper2, dstore=None, constraint=None,
                         reduce=False, det=False):
        """Strengthens the upper bound by intersecting it with upper2.
        If det is True, attempt to determine variable.
        """
        upper = self.get_upper(dstore=dstore)
        if not isinstance(upper, set):
            print("{}'s upper {} is not set".format(self, upper))
        if not upper.issubset(upper2):
            new_upper = upper.intersection(upper2)
            lower_card = self.get_lower_card(dstore=dstore)
            if new_upper == upper:
                return False
            lower = self.get_lower(dstore=dstore)
            if not lower.issubset(new_upper) and constraint:
                s = 'Warning: attempting to change upper bound of {} to {}, which is not a superset of lower bound {}'
                print(s.format(self, new_upper, lower))
            if len(new_upper) < lower_card and constraint:
                s = 'Warning: attempting to change upper bound of {} to {}, which is smaller than lower card {}'
                print(s.format(self, new_upper, lower_card))
            if constraint:
                s = '  {} strengthening upper bound of {} ({}) with {}, now {}'
                print(s.format(constraint, self, upper, upper2, new_upper))
            self.set_upper(new_upper, dstore=dstore)
            if det:
                if new_upper == lower:
#                    print('Determining', self)
                    val_len = len(lower)
                    self.set_value(lower, dstore=dstore)
                    self.set_lower_card(val_len, dstore=dstore)
                    self.set_upper_card(val_len, dstore=dstore)
                    if dstore and self in dstore.undetermined:
                        self.det_update(dstore)
                elif len(new_upper) == lower_card:
                    val_len = lower_card
                    self.set_lower(new_upper, dstore=dstore)
                    self.set_value(new_upper, dstore=dstore)
                    self.set_upper_card(val_len, dstore=dstore)
                    if dstore and self in dstore.undetermined:
                        self.det_update(dstore)
            return True
        return False

    def discard_upper(self, value, dstore=None, constraint=None):
        """Discard set or element from upper bound."""
        upper = self.get_upper(dstore=dstore)
        value = value if isinstance(value, set) else {value}
        if value & upper:
            new_upper = upper - value
            new_upper_card = len(new_upper)
            lower = self.get_lower(dstore=dstore)
            if new_upper_card < len(lower) and constraint:
                s = 'Warning: attempting to discard {} from upper bound {} of {}, making it smaller than lower bound {}'
                print(s.format(value, upper, self, lower))
            lower_card = self.get_lower_card(dstore=dstore)
            if new_upper_card < lower_card:
                s = 'Warning: attempting to discard {} from upper bound {} of {}, making cardinality smaller than {}'
                print(s.format(value, upper, self, lower_card))
            # If value and upper overlap
            if constraint:
                print('  {} discarding {} from {}'.format(constraint, value, self))
            self.set_upper(new_upper, dstore=dstore)
            self.set_upper_card(new_upper_card, dstore=dstore)
            return True
        return False

    def strengthen_lower(self, lower2, dstore=None, constraint=None, det=False):
        """Strengthens the lower bound by unioning it with lower2."""
        lower = self.get_lower(dstore=dstore)
        if not lower.issuperset(lower2):
            new_lower = lower.union(lower2)
            upper = self.get_upper(dstore=dstore)
            upper_card = self.get_upper_card(dstore=dstore)
            if not new_lower.issubset(upper) and constraint:
                s = 'Warning: attempting to change lower bound of {} to {}, which is not a subset of upper bound {}'
                print(s.format(self, new_lower, upper))
            if len(new_lower) > upper_card and constraint:
                s = 'Warning: attempting to change lower bound of {} to {}, which is greater than upper card {}'
                print(s.format(self, new_lower, upper_card))
            if constraint:
                print('  {} strengthening lower bound of {} with {}'.format(constraint, self, lower2))
            self.set_lower(new_lower, dstore=dstore)
            if det:
                if new_lower == upper and upper_card == self.lower_card(dstore=dstore):
                    self.set_value(upper, dstore=dstore)
                    if dstore and self in dstore.undetermined:
                        self.det_update(dstore)
            return True
        return False

    def strengthen_lower_card(self, lower2, dstore=None, constraint=None, det=False):
        """Raises the lower bound on the cardinality of the set."""
        if lower2 > self.get_lower_card(dstore=dstore):
            if constraint:
                print('  {} raising lower cardinality bound of {} to {}'.format(constraint, self, lower2))
            self.set_lower_card(lower2, dstore=dstore)
            if det:
                upper_card = self.get_upper_card(dstore=dstore)
                if lower2 == upper_card:
                    upper = self.get_upper(dstore=dstore)
                    if len(upper) == upper_card:
                        # Determine
                        self.set_lower(upper, dstore=dstore)
                        self.set_value(upper, dstore=dstore)
                        if dstore and self in dstore.undetermined:
                            self.det_update(dstore)
            return True
        return False

    def strengthen_upper_card(self, upper2, dstore=None, constraint=None, det=False):
        """Lowers the upper bound on the cardinality of the set."""
        if upper2 < self.get_upper_card(dstore=dstore):
            if constraint:
                print('  {} lowering upper cardinality bound of {} to {}'.format(constraint, self, upper2))
            self.set_upper_card(upper2, dstore=dstore)
            if det:
                lower_card = self.get_lower_card(dstore=dstore)
                if upper2 == lower_card:
                    lower = self.get_lower(dstore=dstore)
                    if len(lower) == lower_card:
                        # Determine
                        self.set_upper(lower, dstore=dstore)
                        self.set_value(lower, dstore=dstore)
                        if dstore and self in dstore.undetermined:
                            self.det_update(dstore)
            return True
        return False

    ## Printing

    @staticmethod
    def string_range(lower, upper):
        s = '{'
        for i,v in enumerate(upper):
            if i != 0:
                s += ','
            if v not in lower:
                s += '({})'.format(v)
            else:
                s += '{}'.format(v)
        return s + '}'

    def pretty_string(self, dstore=None, spaces=0, end='\n'):
        return '{0}${1}:{2}|{3},{4}|'.format(spaces*' ',
                                             self.name,
                                             Var.string_range(self.get_lower(dstore=dstore),
                                                              self.get_upper(dstore=dstore)),
                                             self.get_lower_card(dstore=dstore),
                                             self.get_upper_card(dstore=dstore))

    def pprint(self, dstore=None, spaces=0, end='\n'):
        print(self.pretty_string(dstore=dstore, spaces=spaces, end=end))

class IVar(Var):

    def __init__(self, name, domain=None,
                 problem=None, dstores=None, rootDS=None,
                 # Vars with low weights are "peripheral".
                 weight=1, essential=True):
        Var.__init__(self, name,
                     lower_domain=set(), upper_domain=domain,
                     lower_card=1, upper_card=1,
                     problem=problem, dstores=dstores, rootDS=rootDS,
                     weight=weight, essential=essential)

    def __repr__(self):
        return '#{}'.format(self.name)

    def equals(self, var, dstore=None, pattern=False):
        """Does this variable have the same value as var in dstore?
        var could be an IVar."""
        value = self.get_value(dstore=dstore)
        var_val = var.get_value(dstore=dstore)
        is_ivar = isinstance(var, IVar)
        if value != None and var_val != None:
            if value == var_val:
                return True
        return False

    def determined(self, dstore=None, constraint=None, verbosity=0):
        """Attempt to determine the variable, returning the value if this is possible,
        False if it's not."""
        val = self.get_value(dstore=dstore)
        if val != None:
            return val
        upper = self.get_upper(dstore=dstore)
        if len(upper) == 1:
            self.set_value(upper, dstore=dstore)
            self.set_lower(upper, dstore=dstore)
            if verbosity > 1:
                print('  {} is determined at {}'.format(self, upper))
            if dstore:
                self.det_update(dstore)
            return upper
        return False

    def pretty_string(self, dstore=None, spaces=0, end='\n'):
        return '{0}#{1}:{2}'.format(spaces*' ',
                                    self.name,
                                    self.get_upper(dstore=dstore))

class LVar(Var):
    """Variable with list values, rather than set."""

    def __init__(self, name,
                 lower_domain=None, upper_domain=None,
                 lower_card=0, upper_card=MAX,
                 problem=None, dstores=None, rootDS=None,
                 constraint=None,
                 # Whether a complete solution depends on a single value for this variable
                 essential=True,
                 # Vars with low weights are "peripheral".
                 weight=1):
        Var.__init__(self, name,
                     lower_domain=lower_domain, upper_domain=upper_domain,
                     lower_card=lower_card, upper_card=upper_card,
                     problem=problem, dstores=dstores, rootDS=rootDS,
                     constraint=constraint,
                     essential=essential,
                     weight=weight)

    def __repr__(self):
        return 'L{}'.format(self.name)

    # Most methods work for both sets and lists

    def equals(self, v):
        """We need something corresponding to set equality. The lists
        might be different lengths because of duplicates."""
        shared = []
        for x in self:
            if x in v:
                shared.append(x)
            else:
                return False
        for x in v:
            if x not in shared:
                return False
        return True

    def bound_fail(self, dstore=None):
        """Fail if the lower bound includes any elements not in the upper bound."""
        return len(self.get_lower(dstore=dstore)) > len(self.get_upper(dstore=dstore))

    def get_undecided(self, dstore=None):
        """Returns the set of values that may or may not be in the variable."""
        dstore = dstore or self.rootDS
        return [x for x in self.get_upper(dstore=dstore) if x not in self.get_lower(dstore=dstore)]

    def determine(self, value, dstore=None, constraint=None):
        """Attempt to determine the variable as value, returning False it can't be
        or if it's already determined."""
        if self.is_determined(dstore=dstore):
            return False
        value = value if isinstance(value, set) else {value}
        orig_upper = self.get_upper(dstore=dstore)
        orig_lower = self.get_lower(dstore=dstore)
        upper = self.get_upper(dstore=dstore)
        if not all([(x in orig_upper) for x in value]):
            # Var can't be determined at this value
            return False
        if constraint:
            print('  {} determining {} as {}'.format(constraint, self, value))
        val_card = len(value)
        self.set_lower(value, dstore=dstore)
        self.set_upper(value, dstore=dstore)
        self.set_value(value, dstore=dstore)
        self.set_lower_card(val_card, dstore=dstore)
        self.set_upper_card(val_card, dstore=dstore)
        if dstore and self in dstore.undetermined:
            self.det_update(dstore)
        if not orig_upper.equals(value) or not orig_lower.equals(value):
            return True
        return False

    def strengthen_upper(self, upper2, dstore=None, constraint=None,
                         reduce=False, det=False):
        """Strengthens the upper bound by intersecting it with upper2.
        If det is True, attempt to determine variable.
        """
        upper = self.get_upper(dstore=dstore)
        if not isinstance(upper, set):
            print("{}'s upper {} is not set".format(self, upper))
        if not all([(x in upper2) for x in upper]):
#        if not upper.issubset(upper2):
            new_upper = [y for y in upper2 if y in upper]
#            new_upper = upper.intersection(upper2)
            lower_card = self.get_lower_card(dstore=dstore)
            if new_upper == upper:
                return False
            lower = self.get_lower(dstore=dstore)
            if not all([(y in new_upper) for y in lower]):
#            if not lower.issubset(new_upper) and constraint:
                s = 'Warning: attempting to change upper bound of {} to {}, which is not a superset of lower bound {}'
                print(s.format(self, new_upper, lower))
            if len(new_upper) < lower_card and constraint:
                s = 'Warning: attempting to change upper bound of {} to {}, which is smaller than lower card {}'
                print(s.format(self, new_upper, lower_card))
            if constraint:
                s = '  {} strengthening upper bound of {} ({}) with {}, now {}'
                print(s.format(constraint, self, upper, upper2, new_upper))
            self.set_upper(new_upper, dstore=dstore)
            if det:
                if new_upper.equals(lower):
#                    print('Determining', self)
                    val_len = len(lower)
                    self.set_value(lower, dstore=dstore)
                    self.set_lower_card(val_len, dstore=dstore)
                    self.set_upper_card(val_len, dstore=dstore)
                    if dstore and self in dstore.undetermined:
                        self.det_update(dstore)
                elif len(new_upper) == lower_card:
                    val_len = lower_card
                    self.set_lower(new_upper, dstore=dstore)
                    self.set_value(new_upper, dstore=dstore)
                    self.set_upper_card(val_len, dstore=dstore)
                    if dstore and self in dstore.undetermined:
                        self.det_update(dstore)
            return True
        return False

    def discard_upper(self, value, dstore=None, constraint=None):
        """Discard set or element from upper bound."""
        upper = self.get_upper(dstore=dstore)
        value = value if isinstance(value, list) else [value]
        if any([x in upper] for x in value):
#        if value & upper:
            new_upper = [y for y in upper if y not in value]
#            new_upper = upper - value
            new_upper_card = len(new_upper)
            lower = self.get_lower(dstore=dstore)
            if new_upper_card < len(lower) and constraint:
                s = 'Warning: attempting to discard {} from upper bound {} of {}, making it smaller than lower bound {}'
                print(s.format(value, upper, self, lower))
            lower_card = self.get_lower_card(dstore=dstore)
            if new_upper_card < lower_card:
                s = 'Warning: attempting to discard {} from upper bound {} of {}, making cardinality smaller than {}'
                print(s.format(value, upper, self, lower_card))
            # If value and upper overlap
            if constraint:
                print('  {} discarding {} from {}'.format(constraint, value, self))
            self.set_upper(new_upper, dstore=dstore)
            self.set_upper_card(new_upper_card, dstore=dstore)
            return True
        return False

    def strengthen_lower(self, lower2, dstore=None, constraint=None, det=False):
        """Strengthens the lower bound by unioning it with lower2."""
        lower = self.get_lower(dstore=dstore)
        if not all([(x in lower) for x in lower2]):
#        if not lower.issuperset(lower2):
            # eliminate duplicates
            new_lower = lower + [y for y in lower2 if y not in lower]
#            new_lower = lower.union(lower2)
            upper = self.get_upper(dstore=dstore)
            upper_card = self.get_upper_card(dstore=dstore)
            if not all([(y in new_lower) for y in upper]):
#            if not new_lower.issubset(upper) and constraint:
                s = 'Warning: attempting to change lower bound of {} to {}, which is not a subset of upper bound {}'
                print(s.format(self, new_lower, upper))
            if len(new_lower) > upper_card and constraint:
                s = 'Warning: attempting to change lower bound of {} to {}, which is greater than upper card {}'
                print(s.format(self, new_lower, upper_card))
            if constraint:
                print('  {} strengthening lower bound of {} with {}'.format(constraint, self, lower2))
            self.set_lower(new_lower, dstore=dstore)
            if det:
                if new_lower.equals(upper) and upper_card == self.lower_card(dstore=dstore):
                    self.set_value(upper, dstore=dstore)
                    if dstore and self in dstore.undetermined:
                        self.det_update(dstore)
            return True
        return False

    @staticmethod
    def string_range(lower, upper):
        s = '['
        for i,v in enumerate(upper):
            if i != 0:
                s += ','
            if v not in lower:
                s += '({})'.format(v)
            else:
                s += '{}'.format(v)
        return s + ']'

    def pretty_string(self, dstore=None, spaces=0, end='\n'):
        return '{0}L{1}:{2}|{3},{4}|'.format(spaces*' ',
                                             self.name,
                                             LVar.string_range(self.get_lower(dstore=dstore),
                                                               self.get_upper(dstore=dstore)),
                                             self.get_lower_card(dstore=dstore),
                                             self.get_upper_card(dstore=dstore))

### Variables that are pre-determined.

class DetVar(Var):
    """Pre-determined variable. If DStore is not specified in constructor,
    the variable is determined in all DStores. Should not be modified."""

    def __init__(self, name, value, dstore=None):
        Var.__init__(self, name, rootDS=dstore)
        self.dstore = dstore
        if self.dstore:
            self.determine(value, dstore=dstore)
        else:
            self.value = value
        self.lower_domain = value
        self.upper_domain = value
        self.set_cards(value)

    def __repr__(self):
        return '$!{}:{}'.format(self.name, self.value)

    def set_cards(self, value):
        self.init_upper_card = len(value)
        self.init_lower_card = len(value)

    def init_values(self, dstore=None):
        # Don't do anything
        pass

    def set(self, dstore, feature, value):
        """Override set in Variable to prevent changes."""
        # This message should print out under some verbosity conditions.
        s = 'Warning: attempting to change pre-determined variable {}, feature: {}, value: {}, orig value: {}'
        print(s.format(self, feature, value, self.get(dstore, feature)))
        return False

    def is_determined(self, dstore=None):
        return True

    def pretty_string(self, dstore=None, spaces=0, end='\n'):
        return '{0}$!{1}:{2}'.format(spaces*' ', self.name, self.get(dstore, 'value'))

    def cost(self, dstore=None):
        return 0

    def determined(self, dstore=None, verbosity=0, constraint=None):
        if self.dstore:
            return Var.determined(self, dstore=dstore, verbosity=verbosity, constraint=constraint)
        return self.value

    def get(self, dstore, feature, default=None):
        if self.dstore:
            return Var.get(self, dstore, feature, default=default)
        if feature in {'value', 'lower', 'upper'}:
            return self.value
        if feature in {'lower_card', 'upper_card'}:
            return len(self.value)

    def get_undecided(self, dstore=None):
        return set()

class DetIVar(DetVar, IVar):

    def __init__(self, name='', value=0, dstore=None):
        IVar.__init__(self, name, rootDS=dstore)
        # value could be the empty set
        if not isinstance(value, set):
            value = {value}
        DetVar.__init__(self, name, value, dstore)
        self.init_domain = value
        self.default_value = value

    def __repr__(self):
        return '#!{}:{}'.format(self.name, list(self.value)[0])

    def init_values(self, dstore=None):
        # Don't do anything
        pass

    def set_cards(self, value):
        self.init_upper_card = 1
        self.init_lower_card = 1

    def pretty_string(self, dstore=None, spaces=0, end='\n'):
        return '{0}#!{1}:{2}'.format(spaces*' ', self.name, self.get(dstore, 'value'))

    def get(self, dstore, feature, default=None):
        if self.dstore:
            return IVar.get(self, dstore, feature, default=default)
        if feature == 'value':
            return self.value
        if feature in ('dom', 'upper', 'lower'):
            if isinstance(self.value, set):
                return self.value
            else:
                return {self.value}
        if feature in ('lower_card', 'upper_card'):
            return 1

class DetLVar(DetVar):
    """Pre-determined list variable. If DStore is not specified in constructor,
    the variable is determined in all DStores. Should not be modified."""

    def __init__(self, name, value, dstore=None):
        DetVar.__init__(self, name, value, dstore=dstore)

    def __repr__(self):
        return 'L!{}:{}'.format(self.name, self.value)

    def pretty_string(self, dstore=None, spaces=0, end='\n'):
        return '{0}L!{1}:{2}'.format(spaces*' ', self.name, self.get(dstore, 'value'))

    def get_undecided(self, dstore=None):
        return []

class VarError(Exception):
    '''Class for errors encountered when attempting to execute an event on a variable.'''

    def __init__(self, value):
        self.value = value

    def __str__(self):
        return repr(self.value)

# Constant variables, determined in all DStores
EMPTY = DetVar("empty", set())
