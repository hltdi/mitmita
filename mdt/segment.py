#   
#   Mit'mit'a: sentences and solution segments
#
########################################################################
#
#   This file is part of the MDT project of the PLoGS metaproject
#   for parsing, generation, translation, and computer-assisted
#   human translation.
#
#   Copyleft 2014, 2015, 2016, 2017; HLTDI, PLoGS <gasser@indiana.edu>
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

# 2016.01.05
# -- Split off from sentence.py
# 2016.01.06
# -- Added SolSeg class for sentence solution segments with translations.
# 2016.01.18
# -- Fixed TreeTrans.build() so that multiple translations work with groups involving merging.
# 2016.01.26
# -- Fixed it so that groups can have multiple abstract nodes, for example, <por $num $n>, and
#    match concrete nodes in multiple other groups.
# 2016.02.01
# -- Cache added to TreeTrans to save feature and node merger information during build, preventing
#    repetition.
# 2016.03.02
# -- Lots of changes to how segments are displayed in GUI, especially including radio buttons for
#    choices.
# 2016.03.06
# -- GInsts create GNodes only for tokens that fail to get deleted by MorphoSyns. So there may be
#    gaps in GNode indices.
# 2016.03.08
# -- SolSeg.set_html() also creates a dict of choice alternatives.
# 2016.06.01
# -- GNodes now carry sets of features rather than a single feature. This solves a problem with
#    failure to match features in node merging in the case of an ambiguous analysis of the concrete node.
# 2016.06.15
# -- Finally fixed build() so it correctly applies to each combination of group translation for top-level
#    and subtree groups.
# 2016.06.16
# -- OK, I still wasn't quite finished.
# 2017.03
# -- Display for GInsts improved.
# 2017.04.24
# -- Got things to work with external tagger (not many changes).
# 2017.06.22
# -- Skip group item matching for punctuation nodes.
#    Character joining items in phrases and numerals is now ~ instead of _.

import itertools, copy, re
from .cs import *
from mdt.morphology.semiring import FSSet
# needed for a few static methods
from .entry import Entry, Group
from .record import SegRecord
from .utils import *

class SolSeg:
    """Sentence solution segment, realization of a single Group. Displayed in GUI."""

    # colors to display segments in interface
    tt_colors = ['blue', 'sienna', 'green', 'purple', 'red', 'blue', 'sienna', 'green', 'purple', 'red', 'blue', 'sienna', 'green',
                 'purple', 'red', 'blue', 'sienna', 'green', 'purple', 'red', 'blue', 'sienna', 'green',
                 'purple', 'red', 'blue', 'sienna', 'green', 'purple', 'red', 'blue', 'sienna', 'green',
                 'purple', 'red', 'blue', 'sienna', 'green', 'purple', 'red', 'blue', 'sienna', 'green',
                 'purple', 'red', 'blue', 'sienna', 'green', 'purple', 'red', 'blue', 'sienna', 'green']

    tt_notrans_color = "Gray"

    special_re = re.compile("%[A-Z]+_")

    def __init__(self, solution, indices, translation, tokens, color=None,
                 spec_indices=None, session=None, gname=None, merger_groups=None, is_punc=False):
        self.source = solution.source
        self.target = solution.target
        self.indices = indices
        # Are there any alternatives among the translations?
        self.any_choices = any(['|' in t for t in translation])
        # For each translation alternative, separate words, each of which can have alternatives (separated by '|').
        self.translation = [t.split() for t in translation]
        self.tokens = tokens
        self.token_str = ' '.join(tokens)
        self.raw_token_str = self.token_str[:]
        # If there are special tokens in the source language, fix them here.
        self.special = False
        if '%' in self.token_str:
            self.token_str = SolSeg.remove_spec_pre(self.token_str).replace('~', ' ')
            self.special = True
            if not translation:
                # Set the translation for the special segment
                spec_trans = self.source.translate_special(tokens[0])
                if spec_trans:
                    self.translation = [[spec_trans]]
        self.color = color
        # Whether this segment is just punctuation
        self.is_punc = is_punc
        # Name of the group instantiated in this segment
        self.gname = gname
        # Triples for each merger with the segment
        self.merger_gnames = merger_groups
        self.session = session
        # Create a record for this segment if there's a session running and it's not punctuation
        if session and session.running and not self.is_punc:
            self.record = self.make_record(session, solution.sentence)
        else:
            self.record = None
        self.html = []
        print("Creating SolSeg {} with solution {}, indices {}, translation {}, tokens {}, is punc? {}".format(self, solution, indices, translation, tokens, is_punc))

    def __repr__(self):
        """Print name."""
        return ">>{}<<".format(self.token_str)

    @staticmethod
    def remove_spec_pre(string):
        """Remove special prefixes, for example, '%ND_'."""
        if '%' in string:
            string = ''.join(SolSeg.special_re.split(string))
        return string
    
    def make_record(self, session=None, sentence=None):
        """Create the SegRecord object for this SolSeg."""
        if sentence:
            return SegRecord(self, sentence=sentence.record, session=session)

    def set_html(self, index, verbosity=0):
        """Set the HTML markup for this segment, given its position in the sentence,
        and the dictionary of choices for the record of the SolSeg.
        Do postprocessing on phrases joined by '_' or special tokens (numerals).
        """
        # Combine translations where possible
        if self.special:
            print("Setting HTML for special segment {}".format(self.raw_token_str))
        self.color = SolSeg.tt_notrans_color if not self.translation else SolSeg.tt_colors[index]
        transhtml = '<table>'
        capitalized = False
        choice_list = self.record.choices if self.record else None
        # Final source segment output
        tokens = self.token_str
        if self.is_punc:
            trans = self.translation[0][0]
            transhtml += "<tr><td class='transchoice'>"
            transhtml += '<br/><input type="radio" name="choice" id={} value="{}" checked>{}</td>'.format(trans, trans, trans)
            transhtml += '</tr>'
            transhtml += '<tr><td class="other">'
            transhtml += '<input type="radio" name="choice" id="other" value="other">other translation (enter below)</td></tr>'
            transhtml += '</table>'
            self.html = (tokens, self.color, transhtml)
            return
        for tindex, t in enumerate(self.translation):
            print("{} setting HTML for {}: {}".format(self, tindex, t))
            # Create all combinations of word sequences
            t_expanded = []
            for tt in t:
                if '(' in tt:
                    tt = ['', tt[1:-1]]
                else:
                    tt = tt.split('|')
                t_expanded.append(tt)
            tcombs = [' '.join(y) for y in allcombs(t_expanded)]
            tcombs.sort()
#            print("  Tcombs {}".format(tcombs))
            # A single translation of the source segment
            transhtml += '<tr>'
            transhtml += "<td class='transchoice'>"
            html_choices = []
            for tcindex, tchoice in enumerate(tcombs):
                if tindex == 0 and tcindex == 0:
                    html_choices.append('<input type="radio" name="choice" id={} value="{}" checked>{}'.format(tchoice, tchoice, tchoice))
                else:
                    html_choices.append('<input type="radio" name="choice" id={} value="{}">{}'.format(tchoice, tchoice, tchoice))
            transhtml += "<br/>".join(html_choices)
            transhtml += "</td>"
            if self.record:
                choice_list.append(tchoice)
            transhtml += '</tr>'
        if self.translation:
            # Add other translation button
            # Button to translate as source language
            if not self.is_punc:
                transhtml += '<tr><td class="source">'
                transhtml += '<input type="radio" name="choice" id={} value="{}">{}</td></tr>'.format(tokens, tokens, tokens)
            # Button for the user's own translation
            transhtml += '<tr><td class="other">'
            transhtml += '<input type="radio" name="choice" id="other" value="other">other translation (enter below)</td></tr>'
            # Remove special prefixes
            transhtml = SolSeg.remove_spec_pre(transhtml)
            transhtml = transhtml.replace('_', ' ')
            transhtml = transhtml.replace('~', ' ')
        else:
            # No translations suggested: buttons for 'your translation' and 'translate as source'
            # Button to translate as source language
            transhtml += '<tr><td class="source">'
            transhtml += '<input type="radio" name="choice" id={} value="{}">{}</td></tr>'.format(tokens, tokens, tokens)
            # Add other translation button
            transhtml += '<tr><td class="other">'
            transhtml += '<input type="radio" name="choice" id="other" value="other" checked>other translation (enter below)</td></tr>'
            # Remove special prefixes
            transhtml = SolSeg.remove_spec_pre(transhtml)
            transhtml = transhtml.replace('_', ' ')
        transhtml += '</table>'
        # Capitalize tokens if in first place        
        if index==0:
            capitalized = False
            if ' ' in tokens:
                toks = []
                tok_list = tokens.split()
                for tok in tok_list:
                    if capitalized:
                        toks.append(tok)
                    elif self.source.is_punc(tok):
                        toks.append(tok)
                    else:
                        toks.append(tok.capitalize())
                        capitalized = True
                tokens = ' '.join(toks)
            else:
                tokens = tokens.capitalize()
        self.html = (tokens, self.color, transhtml, index)

    @staticmethod
    def list_html(segments):
        """Set the HTML for the list of segments in a sentence."""
        for i, segment in enumerate(segments):
            segment.set_html(i)

class SNode:
    """Sentence token and its associated analyses and variables."""

    def __init__(self, token, index, analyses, sentence, raw_indices,
                 rawtoken=None): #, del_indices=None):
#        print("Creating SNode with args {}, {}, {}, {}".format(token, index, analyses, sentence))
        # Raw form in sentence (possibly result of segmentation)
        self.token = token
        # Original form of this node's token (may be capitalized)
        self.rawtoken = rawtoken
        # Position in sentence
        self.index = index
        # Positions in original sentence
        self.raw_indices = raw_indices
#        # Positions of deleted tokens
#        self.del_indices = del_indices or []
        # List of analyses
        if analyses and not isinstance(analyses, list):
            analyses = [analyses]
        if not analyses:
            analyses = [{'root': token}]
        self.analyses = analyses
        # Back pointer to sentence
        self.sentence = sentence
        # Raw sentence tokens associated with this SNode
#        print("Tokens {}".format(sentence.tokens))
#        print("Raw indices {}".format(self.raw_indices))
        self.raw_tokens = [sentence.tokens[i] for i in self.raw_indices]
        # Any deleted tokens to the left or right of the SNode token
        self.left_delete = None
        self.right_delete = None
        token_headi = self.raw_tokens.index(self.token)
        if token_headi != 0:
            self.left_delete = self.raw_tokens[:token_headi]
        if token_headi != len(self.raw_tokens) - 1:
            self.right_delete = self.raw_tokens[token_head1:]
        # We'll need these for multiple matchings
        self.cats = self.get_cats()
        # Indices of candidate gnodes for this snode found during lexicalization
        self.gnodes = None
        # Dict of variables specific to this SNode
        self.variables = {}
        ## Tokens in target language for this SNode
        self.translations = []
        ## Groups found during candidate search
        self.group_cands = []
#        print("Analysis for {}: {}".format(self, self.analyses))

    def __repr__(self):
        """Print name."""
        return "*{}:{}".format(self.token, self.index)

    def get_analysis(self):
        """The single analysis for this node."""
        return self.analyses[0]

    def is_punc(self):
        """Is this node a punctuation node?"""
        return self.get_analysis().get('pos') == 'pnc'

    def is_unk(self):
        """Does this node have no analysis, no known category or POS?"""
        a = self.get_analysis()
        return not (a.get('pos') or a.get('cats') or a.get('features'))

    ## Create IVars and (set) Vars with sentence DS as root DS

    def ivar(self, key, name, domain, ess=False):
        self.variables[key] = IVar(name, domain, rootDS=self.sentence.dstore,
                                   essential=ess)

    def svar(self, key, name, lower, upper, lower_card=0, upper_card=MAX,
             ess=False):
        self.variables[key] = Var(name, lower, upper, lower_card, upper_card,
                                  rootDS=self.sentence.dstore, essential=ess)

    def lvar(self, key, name, lower, upper, lower_card=0, upper_card=MAX,
             ess=False):
        self.variables[key] = LVar(name, lower, upper, lower_card, upper_card,
                                   rootDS=self.sentence.dstore, essential=ess)

    def create_variables(self, verbosity=0):
        if not self.gnodes:
            # Nothing matched this snode; all variables empty
            self.variables['gnodes'] = EMPTY
            self.variables['cgnodes'] = EMPTY
            self.variables['agnodes'] = EMPTY
#            self.variables['mgnodes'] = EMPTY
            self.variables['features'] = EMPTY
        else:
            # GNodes associated with this SNode: 0, 1, or 2
            upper = set(self.gnodes)
            self.svar('gnodes', "w{}->gn".format(self.index), set(),
                      upper,
                      0, 2, ess=True)
            # Concrete GNodes associated with this SNode: must be 1
            self.svar('cgnodes', "w{}->cgn".format(self.index), set(),
                      {gn.sent_index for gn in self.sentence.gnodes if not gn.cat},
                      1, 1)
            # Abstract GNodes associated with this SNode: 0 or 1
            self.svar('agnodes', "w{}->agn".format(self.index), set(),
                      {gn.sent_index for gn in self.sentence.gnodes if gn.cat},
                      0, 1)
            # Features
            features = self.get_features()
            if len(features) > 1:
                self.lvar('features', 'w{}f'.format(self.index),
                          [], features, 1, 1)
            else:
                # Only one choice so features are determined for this SNode
                self.variables['features'] = DetLVar('w{}f'.format(self.index), features)

    def get_cats(self):
        """The set of categories for the node's token, or None."""
        if not self.analyses:
            return None
        cats = set()
        for analysis in self.analyses:
            if 'cats' in analysis:
                cats.update(analysis['cats'])
        return cats

    def get_features(self):
        """The list of possible FeatStruct objects for the SNode."""
        features = []
        if self.analyses:
            for analysis in self.analyses:
                if 'features' in analysis:
                    features.append(analysis['features'])
                else:
                    features.append(FeatStruct({}))
        return features

    def neg_match(self, grp_specs, verbosity=0, debug=False):
        """Does this node match a negative group condition, with grp_spec either a FeatStruc
        or a category? Look through analyses until one *fails* to match."""
        for grp_spec in grp_specs:
#            print("Neg match: {}".format(grp_spec))
            matched = True
            # See if any analysis fails to match this grp_spec; if not succeed
            for analysis in self.analyses:
#                print(" {}".format(analysis))
                if isinstance(grp_spec, str):
                    sn_cats = analysis.get('cats', [])
                    if grp_spec in sn_cats or grp_spec == analysis.get('pos'):
                        # Matches, keep looking
                        continue
                    else:
                        matched = False
                        # Go to next grp_spec
                        break
                else:
                    sn_feats = analysis.get('features')
                    if sn_feats:
                        u_features = sn_fats.unify_FS(grp_spec, strict=True, verbose=verbosity>1)
                        if u_features != 'fail':
                            # Matches, keep looking
                            continue
                        else:
                            matched = False
                            # Go to next grp_spec
                            break
                    else:
                        matched = False
                        # Go to next grp_spec
                        break
#            print(" Matched: {}".format(matched))
            if matched:
                return True
        # None matched
        return False

    def match(self, grp_item, grp_feats, verbosity=0):
        """Does this node match the group item (word, root, category) and
        any features associated with it?"""
        # If this is a punctuation node, it can't match a group item unless the item is also punctuation (not alphanum)
        if self.is_punc() and grp_item.isalnum():
            return False
        if verbosity > 1:
            print('   SNode {} with features {} trying to match item {} with features {}'.format(self, self.analyses, grp_item, grp_feats.__repr__()))
        # If item is a category, don't bother looking at token
        is_cat = Entry.is_cat(grp_item)
        is_spec = Entry.is_special(grp_item)
        if is_spec and Entry.is_special(self.token):
#            print("Special entry {} for {}".format(grp_item, self.token))
            token_type = self.token.split('~')[0]
            if token_type.startswith(grp_item):
                # Special group item matches node token (grp_item could be shorter than token_type)
                return None
        if not self.analyses:
            # The node has no associated roots, cats, or features.
            if self.token == grp_item:
                if verbosity:
                    print("    Non-cat token matches node token")
                # Exact match between group and node tokens. SUCCEED with no features
                return None
            else:
                # All other cases fail because root or cat matches require node features
                return False
        else:
            # Check whether a group item is really a set item (starting with '$$'); if so, drop the first '$' before matching
            if is_cat and Entry.is_set(grp_item):
                grp_item = grp_item[1:]
            # If group token is not cat and there are no group features, check for perfect match
            if not is_cat and not grp_feats:
                if self.token == grp_item:
                    if verbosity:
                        print("    Matches trivially")
                    return None
            # Go through analyses, checking cat, root, and features (if any group features)
            results = []
            for analysis in self.analyses:
                node_features = analysis.get('features')
                node_cats = analysis.get('cats', [])
                node_root = analysis.get('root', '')
                node_roots = None
                if verbosity > 1:
                    print("    Trying to match analysis: {}/{}/{} against group {}".format(node_root, node_cats, node_features.__repr__(), grp_item))
                if '_' in node_root: # and not SolSeg.special_re.match(node_root):
                    # Numbers and other special tokens also contain '_'
                    node_roots = []
                    # An ambiguous root in analysis, for example, ser|ir in Spa
#                    node_root_split = node_root.split('_')
#                    if len(node_root_split) != 2:
#                        print("Something wrong with node root {}".format(node_root))
                    r, p = node_root.split('_')
                    for rr in r.split('|'):
                        node_roots.append(rr + '_' + p)
                # Match group token
                if is_cat:
                    if grp_item in node_cats:
                        # The category matches, but is there a group entry for the node's root
                        item_groups = self.sentence.language.groups.get(node_root)
                        if item_groups:
                            if not any([len(g.tokens) == 1 for g in item_groups]):
#                                print("Failing because there is no one-token entry for {}".format(node_root))
                                continue
                        else:
#                            print("Failing because there's no group entry for {}".format(node_root))
                            continue
                    else:
                        # Fail because the group category item doesn't match the node categories
                        continue
                else:
                    # Not a category, has to match the root
                    if node_roots:
                        m = firsttrue(lambda x: x == grp_item, node_roots)
                        if m:
                            node_root = m
                        else:
                            continue
                    elif grp_item != node_root:
                        continue
                # Match features if there are any
                if node_features:
                    if grp_feats:
                        # 2015.7.5: strict option added to force True feature in grp_features
                        # to be present in node_features, e.g., for Spanish reflexive
                        if verbosity > 1:
                            print("    Unifying n feats {} ({}) with g feats {} ({})".format(node_features, type(node_features), grp_feats.__repr__(), type(grp_feats)))
                        nfeattype = type(node_features)
                        if nfeattype == FSSet:
                            u_features = node_features.unify_FS(grp_feats, strict=True, verbose=verbosity>1)
#                            if verbosity > 1:
#                                print("     Result of unification: {}, type {}".format(u_features, type(u_features)))
                        else:
                            u_features = simple_unify(node_features, grp_feats, strict=True)
                        if u_features != 'fail':
                            # SUCCEED: matched token and features
                            results.append((node_root, u_features))
                    else:
                        # SUCCEED: matched token and no group features to match
                        results.append((node_root, node_features))
                else:
                    # SUCCEED: group has features but node doesn't
                    results.append((grp_item, grp_feats))
            if results:
                if verbosity > 1:
                    print("  Returning match results: {}".format(results))
                return results
        return False

class GInst:

    """Instantiation of a group; holds variables and GNode objects."""

    def __init__(self, group, sentence, head_index, snode_indices, index):
#        print("Creating group inst for {} with snode_indices {}".format(group, snode_indices))
        # The Group object that this "instantiates"
        self.group = group
        self.sentence = sentence
        self.target = sentence.target
        # Index of group within the sentence
        self.index = index
        # Index of SNode associated with group head
        self.head_index = head_index
#        self.head_pos = group.pos
        # List of GNodes
        self.nodes = []
        ghead_index = group.head_index
        for index, sntups in enumerate(snode_indices):
            # sntups is a list of snindex, match features, token, create? tuples
#            print(" SNTups {}".format(sntups))
            deleted = False
            for snindex, match, token, create in sntups:
                if not create:
#                    print("token {} doesn't match its snode token".format(token))
                    deleted = True
                    break
            if deleted:
                # If this is before where the head should be, decrement that index
                if index <= ghead_index:
                    ghead_index -= 1
#                print("Ghead index decremented to {}".format(ghead_index))
                # Increment index so indices correspond to raw group tokens
                continue
            else:
                self.nodes.append(GNode(self, index, sntups))
#        self.nodes = [GNode(self, index, indices) for index, indices in enumerate(snode_indices)]
        # The GNode that is the head of this GInst
        if ghead_index > len(self.nodes) - 1:
            print("Problem instantiating {} for {}; head index {}".format(group, self.nodes, ghead_index))
        self.head = self.nodes[ghead_index]
        # Dict of variables specific to this group
        self.variables = {}
        # List of target language groups, gnodes, tnodes
        self.translations = []
        self.ngnodes = len(self.nodes)
        # Number of abstract nodes
        self.nanodes = len([n for n in self.nodes if n.cat])
        # Number of concrete nodes
        self.ncgnodes = self.ngnodes - self.nanodes
        # TreeTrans instance for this GInst; saved here to prevent multiple TreeTrans translations
        self.treetrans = None
        # Indices of GInsts that this GINst depends on; set in Sentence.lexicalize()
        self.dependencies = None
        # Possible snode indices for lexical and category nodes.
        self.sindices = [[], []]
#        print("Creating GInst {} with head i {} and snode indices {}".format(self, head_index, snode_indices))

    def __repr__(self):
        return '<<{}:{}>>'.format(self.group.name, self.group.id)

    def display(self, word_width=10, s2gnodes=None):
        """Show group in terminal."""
        s = '<{}>'.format(self.index).rjust(4)
        n_index = 0
        n = self.nodes[n_index]
        ngnodes = len(self.nodes)
        for gn_indices in s2gnodes:
            if n.sent_index in gn_indices:
                i = '*{}*' if n.head else "{}"
                s += i.format(n.index).center(word_width)
                n_index += 1
                if n_index >= ngnodes:
                    break
                else:
                    n = self.nodes[n_index]
            else:
                s += ' '*word_width
        print(s)

    def pos_pairs(self):
        """Return position constraint pairs for gnodes in the group."""
        gnode_pos = [gn.sent_index for gn in self.nodes]
        return set(itertools.combinations(gnode_pos, 2))

    def gnode_sent_index(self, index):
        """Convert gnode index to gnode sentence index."""
        return self.nodes[index].sent_index

    def get_agr(self):
        """Return agr constraints for group, converted to tuples."""
        result = []
        if self.group.agr:
            for a in copy.deepcopy(self.group.agr):
                feats = [tuple(pair) for pair in a[2:]]
                a[2:] = feats
                # Convert gnode positions to sentence positions
                a[0] = self.gnode_sent_index(a[0])
                a[1] = self.gnode_sent_index(a[1])
                result.append(tuple(a))
        return set(result)

    ## Create IVars and (set) Vars with sentence DS as root DS

    def ivar(self, key, name, domain, ess=False):
        self.variables[key] = IVar(name, domain, rootDS=self.sentence.dstore,
                                   essential=ess)

    def svar(self, key, name, lower, upper, lower_card=0, upper_card=MAX,
             ess=False):
        self.variables[key] = Var(name, lower, upper, lower_card, upper_card,
                                  rootDS=self.sentence.dstore,
                                  essential=ess)

    def create_variables(self, verbosity=0):
        ngroups = len(self.sentence.groups)
        nsnodes = len(self.sentence.nodes)
        cand_snodes = self.sindices[0] + self.sindices[1]
#            self.sentence.covered_indices
#        print("Creating variables for {}, # abs nodes {}".format(self, self.nanodes))
        if self.dependencies:
            self.variables['deps'] = DetVar('deps{}'.format(self.index), self.dependencies)
        else:
            self.variables['deps'] = EMPTY
        # GNode indices for this GInst (determined)
        self.variables['gnodes'] = DetVar('g{}->gnodes'.format(self.index), {gn.sent_index for gn in self.nodes})
        # Abstract GNode indices for GInst (determined)
        if self.nanodes:
            self.variables['agnodes'] = DetVar('g{}->agnodes'.format(self.index), {gn.sent_index for gn in self.nodes if gn.cat})
            # Concrete GNode indices for GInst (determined)
            self.variables['cgnodes'] = DetVar('g{}->cgnodes'.format(self.index), {gn.sent_index for gn in self.nodes if not gn.cat})
        else:
            self.variables['agnodes'] = EMPTY
            self.variables['cgnodes'] = self.variables['gnodes']
        # SNode positions of GNodes for this GInst
        self.svar('gnodes_pos', 'g{}->gnodes_pos'.format(self.index),
                  set(), set(cand_snodes), self.ngnodes, self.ngnodes)
        # SNode positions of abstract GNodes for this GInst
        if self.nanodes == 0:
            # No abstract nodes
            self.variables['agnodes_pos'] = EMPTY
            # SNode positions of concrete GNodes for this GInst
            self.variables['cgnodes_pos'] = self.variables['gnodes_pos']
        else:
            # Position for each abstract node in the group
            self.svar('agnodes_pos', 'g{}->agnodes_pos'.format(self.index),
                      set(), set(cand_snodes), self.nanodes, self.nanodes)
            # Position for each concrete node in the group
            self.svar('cgnodes_pos', 'g{}->cgnodes_pos'.format(self.index),
                      set(), set(cand_snodes), self.ncgnodes, self.ncgnodes)
        # Determined variable for within-source agreement constraints, gen: 0}
        agr = self.get_agr()
        if agr:
            self.variables['agr'] = DetVar('g{}agr'.format(self.index), agr)

    def set_translations(self, verbosity=0):
        """Find the translations of the group in the target language."""
        translations = self.group.get_translations()
        # Sort group translations by their translation frequency
        Group.sort_trans(translations)
#        print("Setting translations for {}: {}".format(self, translations))
#        if verbosity:
#            print("Translations {}".format(translations))
        # If alignments are missing, add default alignment
        for i, t in enumerate(translations):
            if len(t) == 1:
                translations[i] = [t[0], {}]
#                                    {'align': list(range(len(self.nodes)))}]
        ntokens = len(self.group.tokens)
        for tgroup, s2t_dict in translations:
            nttokens = len(tgroup.tokens)
            if verbosity > 1:
                print("   tgroup {}, s2t_dict {}".format(tgroup, s2t_dict))
            # If there's no explicit alignment, it's the obvious default
            if 'align' in s2t_dict:
                alignment = s2t_dict.get('align')
            else:
                alignment = list(range(ntokens))
                for ia, a in enumerate(alignment):
                    if a >= nttokens:
                        alignment[ia] = -1
            if isinstance(tgroup, str):
                # First find the target Group object
                tgroup = self.target.groupnames[tgroup]
#            print("TGroup: {}, alignment {}".format(tgroup, alignment))
            # Make any TNodes (for target words not corresponding to any source words)
            tnodes = []
            if nttokens > ntokens:
                # Target group has more nodes than source group.
                # Indices of groups that are not empty:
                full_t_indices = set(alignment)
                empty_t_indices = set(range(nttokens)) - full_t_indices
                for i in empty_t_indices:
                    empty_t_token = tgroup.tokens[i]
                    empty_t_feats = tgroup.features[i] if tgroup.features else None
                    tnodes.append(TNode(empty_t_token, empty_t_feats, tgroup, i))
            # Deal with individual gnodes in the group
            gnodes = []
            tokens = tgroup.tokens
            features = tgroup.features
            # Go through source group nodes, finding alignments and agreement constraints
            # with target group nodes
#            for gn_index, gnode in enumerate(self.nodes):
            for gnode in self.nodes:
                gn_index = gnode.index
#                print(" tgroup {}, gnode {}, gn_index {}".format(tgroup, gnode, gn_index))
                # Align gnodes with target tokens and features
                targ_index = alignment[gn_index]
                if targ_index < 0:
#                    print("No targ item for gnode {}".format(gnode))
                    # This means there's no target language token for this GNode.
                    continue
                agrs = None
                if s2t_dict.get('agr'):
                    agr = s2t_dict['agr'][gn_index]
                    if agr:
                        tindex, stagr = agr
                        targ_index = tindex
#                        print(" s2t_dict agrs {}, tindex {}, stagr {}".format(agrs, tindex, stagr))
#                    agrs = s2t_dict['agr'][targ_index]
                        agrs = stagr
                token = tokens[targ_index]
                feats = features[targ_index] if features else None
                gnodes.append((gnode, token, feats, agrs, targ_index))
#            print("Gnodes: {}".format(gnodes))
            self.translations.append((tgroup, gnodes, tnodes))

class GNode:

    """Representation of a single node (word, position) within a GInst object."""

    def __init__(self, ginst, index, snodes):
#        print("Creating GNode for {} with snodes {}".format(ginst, snodes))
        self.ginst = ginst
        self.index = index
        self.sentence = ginst.sentence
        self.snode_indices = [s[0] for s in snodes]
        self.snode_anal = [s[1] for s in snodes]
        # Whether this is the head of the group
        self.head = index == ginst.group.head_index
        # Group word, etc. associated with this node
        gtoken = ginst.group.tokens[index]
        self.gtoken = gtoken
        # If this is a set node, use the sentence token instead of the cat name
        if Entry.is_set(gtoken):
            self.token = self.sentence.nodes[snodes[0][0]].token
        else:
            self.token = gtoken
#        self.pos = ''
#        if self.head:
#            self.pos = self.token.partition('_')[-1]
#        print("Getting POS for GNode: {}, {}".format(self.token, self.pos))
        # Whether the associated token is abstract (a category)
        self.cat = Entry.is_cat(self.token)
        # Whether the associated token is special (for example, a numeral).
        self.special = Entry.is_special(self.token)
        # Features associated with this group node
        groupfeats = ginst.group.features
        if groupfeats:
            self.features = groupfeats[index]
        else:
            self.features = None
        self.variables = {}
        # List of target-language token and features associated with this gnode
#        self.translations = []

    def __repr__(self):
        return "{}|{}".format(self.ginst, self.token)

    ## Create IVars and (set) Vars with sentence DS as root DS

    def ivar(self, key, name, domain, ess=False):
        self.variables[key] = IVar(name, domain, rootDS=self.sentence.dstore,
                                   essential=ess)

    def svar(self, key, name, lower, upper, lower_card=0, upper_card=MAX,
             ess=False):
        self.variables[key] = Var(name, lower, upper, lower_card, upper_card,
                                  rootDS=self.sentence.dstore,
                                  essential=ess)

    def create_variables(self, verbosity=0):
        nsnodes = len(self.sentence.nodes)
        # SNode index for this GNode
        self.ivar('snodes', "gn{}->w".format(self.sent_index), set(self.snode_indices))

class TNode:

    """Representation of a node within a target language group that doesn't
    have a corresponding node in the source language group that it's the
    translation of."""

    def __init__(self, token, features, group, index):
        self.token = token
        self.features = features
        self.group = group
#        self.sentence = ginst.sentence
        self.index = index

    def generate(self, verbosity=0):
        """Generate forms for the TNode."""
        print("Generating form for target token {} and features {}".format(self.token, self.features))
        if Entry.is_lexeme(self.token):
            return self.sentence.target.generate(self.token, self.features)
        else:
            return [self.token]

    def __repr__(self):
        return "~{}|{}".format(self.ginst, self.token)

class TreeTrans:
    """Translation of a tree: a group or two or more groups joined by merged nodes."""

    def __init__(self, solution, tree=None, ginst=None,
                 abs_gnode_dict=None, gnode_dict=None, group_attribs=None,
                 # Whether the tree has any abstract nodes (to merge with concrete nodes)
                 any_anode=False,
#                 attribs=None,
                 index=0, top=False, verbosity=0):
        # The solution generating this translation
        self.solution = solution
        self.source = solution.source
        self.target = solution.target
        self.sentence = solution.sentence
        # Dict keeping information about each gnode; this dict is shared across different TreeTrans instances
        self.abs_gnode_dict = abs_gnode_dict
        self.gnode_dict = gnode_dict
        # A set of sentence node indices
        self.tree = tree
        # Target position indices
        self.ttree = set()
        # TTs contained within this TT
        self.subTTs = []
        # Whether this is the top of a tree
        self.top = top
        # All target groups for nodes within this TT
        self.all_tgroups = []
        # Merged group indices
        self.mergers = []
        snode_indices = list(tree)
        snode_indices.sort()
        self.snode_indices = snode_indices
        self.snodes = [self.sentence.nodes[i] for i in snode_indices]
        self.sol_gnodes_feats = [solution.gnodes_feats[i] for i in snode_indices]
        self.nodes = []
        # The GInst at the top of the tree
        self.ginst = ginst
        # Save this TreeTrans in the GInst
        ginst.treetrans = self
        self.index = index
        self.any_anode = any_anode
        self.group_attribs = group_attribs or []
        # Translation groups
        self.tgroups = [g[0] for g in group_attribs]
        # TNodes
        self.tnodes = [g[1] for g in group_attribs]
        # Root domain store for variables
        self.dstore = DStore(name="TT{}".format(self.index))
        # Order variables for each node, tree variables for groups
        self.variables = {}
        # pairs of node indices representing order constraints
        self.order_pairs = []
        # Order and disjunction constraints
        self.constraints = []
        self.solver = Solver(self.constraints, self.dstore, description='target tree realization',
                             verbosity=verbosity)
#        # Positions of target words
#        self.positions = []
        # These are produced in self.build()
        self.node_features = None
        self.group_nodes = None
        self.agreements = None
        # Final outputs; different ones have alternate word orders
        self.outputs = []
        # Strings representing outputs
        self.output_strings = []
        # Cache for node mergers
        self.cache = {}
        if verbosity:
            print("Created TreeTrans {}".format(self))
            print("  Indices: {}".format(self.tree))
            print("  Sol gnodes feats: {}".format(self.sol_gnodes_feats))

    def __repr__(self):
        return "{{{}}}->".format(self.ginst)

    def get_merger_groups(self):
        """A list of triples for each merger: gnode index within top-level group,
        index of concrete gnode within its group, name of group for concrete node."""
        groups = []
        for index, gnodes in enumerate([s[0] for s in self.sol_gnodes_feats]):
            # A single gnode means no merger
            if len(gnodes) == 1:
                continue
            # A merger, find the concrete gnode
            concgn = gnodes[0]
            if gnodes[0].cat:
                concgn = gnodes[1]
            groups.append((index, concgn.index, concgn.ginst.group.name))
        return groups

    def get_merger_roots(self):
        """A list of triples for each merger: gnode index within top-level group,
        index of concrete gnode within its group, group head (root) for concrete node."""
        roots = []
        for index, gnodes in enumerate([s[0] for s in self.sol_gnodes_feats]):
            # A single gnode means no merger
            if len(gnodes) == 1:
                continue
            # A merger, find the concrete gnode
            concgn = gnodes[0]
            if gnodes[0].cat:
                concgn = gnodes[1]
            roots.append((index, concgn.index, concgn.ginst.group.head))
        return roots
        
    def display(self, index):
        print("{}  {}".format(self, self.output_strings[index]))

    def display_all(self):
        for index in range(len(self.outputs)):
            self.display(index)

    @staticmethod
    def output_string(output):
#        print("Converting output {} to string".format(output))
        l = []
        for word_list in output:
            if len(word_list) == 1:
                l.append(word_list[0])
            else:
                l.append('|'.join(word_list))
        string = ' '.join(l)
        # _ is a placeholder for space
#        string = string.replace('_', ' ')
        return string

    def build(self, tg_groups=None, tg_tnodes=None, verbosity=0):
        """Unify translation features for merged nodes, map agr features from source to target,
        generate surface target forms from resulting roots and features.
        tg_groups is a combination of target groups.
        THIS IS WAY TOO COMPLICATED; SIMPLIFY IT.
        """
        if verbosity:
            print('BUILDING {} with tgroups {} and tnodes {}'.format(self, tg_groups, tg_tnodes))
            print("  SNodes: {}".format(self.snodes))
        tnode_index = 0
        # Dictionary mapping source node indices to initial target node indices
        node_index_map, agreements, group_nodes = {}, {}, {}
        node_features = []
        # reinitialize mergers
        self.mergers = []
        # Find the top-level tgroup
        top_group_attribs = list(itertools.filterfalse(lambda x: x[0] not in tg_groups, self.group_attribs))[0]
        if verbosity:
            print('Top group attribs: {}'.format(top_group_attribs))
        for snode, (gnodes, features) in zip(self.snodes, self.sol_gnodes_feats):
            if verbosity:
                fstring = "   snode {}, gnodes {}, features {}, tnode index {}"
                print(fstring.format(snode, gnodes, features.__repr__(), tnode_index))
            if not gnodes:
                # snode is not covered by any group
                node_index_map[snode.index] = tnode_index
                node_features.append([snode.token, None, []])
                tnode_index += 1
            elif len(gnodes) == 1 and gnodes[0].special:
                gnode = gnodes[0]
                # This is where a special node gets translated; by default, source language form is used.
                spec_token = snode.token
                spec_trans = self.source.translate_special(spec_token)
                print("Translating {} as {}".format(spec_token, spec_trans))
                gnode_tuple_list = self.gnode_dict[gnode]
                gnode_tuple = firsttrue(lambda x: x[0] in tg_groups, gnode_tuple_list)
                if verbosity > 1:
                    print("   gnode_tuple: {}".format(gnode_tuple))
                tgroup, token, targ_feats, agrs, t_index = gnode_tuple
                node_index_map[snode.index] = tnode_index
                # Constrain the position of this node in the tgroup
                if len(tgroup.tokens) > 1:
                    t_indices = [(tgroup, t_index)]
                node_features.append([spec_trans, None, t_indices])
                tnode_index += 1
            else:
                cache_key = None
                gna, gnc, token = None, None, None
                targ_feats, agrs = None, None
                t_indices = []
                if verbosity:
                    if len(gnodes) > 1:
                        print("  multiple gnodes: {}".format(gnodes))
                if gnodes[0] in self.abs_gnode_dict and len(gnodes) > 1:
#                    if verbosity:
#                        print("   {}: gnodes {} contain an abs gnode dict in first position".format(self, gnodes))
                    gna = self.abs_gnode_dict[gnodes[0]]
                    gnc = self.gnode_dict[gnodes[1]]
                elif len(gnodes) > 1 and gnodes[1] in self.abs_gnode_dict:
#                    if verbosity:
#                        print("   {}: gnodes {} contain an abs gnode dict in second position".format(self, gnodes))
                    gna = self.abs_gnode_dict[gnodes[1]]
                    gnc = self.gnode_dict[gnodes[0]]
                if gna:
                    # Two nodes to be merged
                    if verbosity > 1:
                        print("   gna: {}".format(gna))
                        print("   gnc: {}".format(gnc))
                    gnc1 = firsttrue(lambda x: x[0] in tg_groups, gnc)
                    if verbosity:
                        print("   concrete gnode tuple: {}".format(gnc1))
                    gna1 = firsttrue(lambda x: x[0] in tg_groups, gna)
                    if verbosity:
                        print("   abstract gnode tuple: {}".format(gna1))
                    # There are two gnodes for this snode, one concrete, one abstract;
                    # gna and gnc are lists of tuples for different translations
                    if verbosity > 1 and len(gnc) > 1:
                        print("   multiple translations for concrete node: {}".format(gnc))
                    if verbosity > 1and len(gna) > 1:
                        print("   multiple translations for abstract node: {}".format(gna))
                    if verbosity:
                        print("   merging nodes: concrete {}, abstract {}".format(gnc1, gna1))
                    cache_key = ((gnc1[0], gnc1[-1]), (gna1[0], gna1[-1]))
                    if cache_key in self.cache:
                        tok, tn_i, t_i, tg, t_feats = self.cache[cache_key]
                        if verbosity > 1:
                            print("   merger already in cache: {}".format(self.cache[cache_key]))
                        self.mergers.append((tn_i, tg))
                        if verbosity > 1:
                            print("   mergers for {}: {}".format(self, self.mergers))
                        node_index_map[snode.index] = tn_i
                        feat_index = len(node_features)
                        node_features.append([tok, t_feats, t_i])
                        for t_index in t_i:
                            group_nodes[t_index] = [tok, t_feats, feat_index]
                    else:
                        tgroups, tokens, targ_feats, agrs, t_index = zip(gna1, gnc1)
#                        print("   tgroups {}, tokens {}".format(tgroups, tokens))
                        token = tokens[1]
                        targ_feats = FeatStruct.unify_all(targ_feats)
                        if targ_feats == 'fail':
                            print("Features fail to unify")
                            return False
                        # Merge the agreements
                        agrs = TreeTrans.merge_agrs(agrs)
                        t_indices.append((tgroups[0], gna1[-1]))
                        t_indices.append((tgroups[1], gnc1[-1]))
                        ## Record this node and its groups in mergers
                        tg = list(zip(tgroups, gnodes))
                        # Sort the groups by which is the "outer" group in the merger
                        tg.sort(key=lambda x: x[1].cat)
                        tg = [x[0] for x in tg]
                        if verbosity:
                            print("   creating merger {} for snode index {}, tnode index {}".format(tg, snode.index, tnode_index))
                        self.mergers.append((tnode_index, tg))
                        # Make target and source features agree as required
                        if not targ_feats:
                            targ_feats = FeatStruct({})
                        if agrs:
                            # Use an (unfrozen) copy of target features
                            targ_feats = targ_feats.copy(True)
                            if verbosity:
                                print("  Causing sfeats {} to agree with tfeats {}".format(features, targ_feats))
                            if features:
                                # features may be None
                                targ_feats = features.agree_FSS(targ_feats, agrs)
                            if verbosity:
                                print("   Now: {} to agree with tfeats {}".format(features, targ_feats))
                        node_index_map[snode.index] = tnode_index
                        feat_index = len(node_features)
                        node_features.append([token, targ_feats, t_indices])
                        for t_index in t_indices:
                            group_nodes[t_index] = [token, targ_feats, feat_index]
                        self.cache[cache_key] = (token, tnode_index, t_indices, tg, targ_feats)
                    
                else:
                    # only one gnode in list
                    gnode = gnodes[0]
                    if verbosity > 1:
                        print("   single node to generate: {}".format(gnode))
                    if gnode not in self.gnode_dict:
                        if verbosity > 1:
                            print("   not in gnode dict, skipping")
                        # But if this is the head of the TreeTrans's group, we need to increment the tnode_index
#                        if gnode == self.ginst.head:
#                            if verbosity:
#                                print("   gnode is head of TT group")
                            tnode_index += 1
                        continue
                    else:
                        # Translation (target) group for this instance of build() and this node
#                        tgroup1 = tg_groups[tnode_index]
                        gnode_tuple_list = self.gnode_dict[gnode]
                        gnode_tuple = firsttrue(lambda x: x[0] in tg_groups, gnode_tuple_list)
#                        print("gnode {}".format(gnode))
#                        print(" tgcomb {}".format(tg_groups))
#                        print(" gnode_tuple_list {}".format(gnode_tuple_list))
                        if verbosity > 1:
                            print("   gnode_tuple: {}".format(gnode_tuple))
                        if not gnode_tuple:
                            print("Something wrong")
                        tgroup, token, targ_feats, agrs, t_index = gnode_tuple
                        cache_key = tgroup, t_index
                        if cache_key in self.cache:
                            tok, tn_i, t_i, x, t_feats = self.cache[cache_key]
                            if verbosity > 1:
                                print("   single node already in cache: {}".format(self.cache[cache_key]))
                            node_index_map[snode.index] = tn_i
                            feat_index = len(node_features)
                            node_features.append([tok, t_feats, t_i])
                            for t_ind in t_i:
                                group_nodes[t_ind] = [tok, t_feats, feat_index]
                        else:
                            if len(tgroup.tokens) > 1:
                                t_indices.append((tgroup, t_index))
                            # Make target and source features agree as required
                            if not targ_feats:
                                targ_feats = FeatStruct({})
                            if agrs:
                                if verbosity:
                                    print("  Causing sfeats {} to agree with tfeats {}".format(features, targ_feats.__repr__()))
                                    print("    features type: {}".format(type(features)))
                                if features:
                                    # features could be None
                                    targ_feats = features.agree_FSS(targ_feats, agrs)
                                if verbosity:
                                    print("  Now {} and {}".format(features, targ_feats.__repr__()))
                            node_index_map[snode.index] = tnode_index
                            feat_index = len(node_features)
                            node_features.append([token, targ_feats, t_indices])
                            for t_ind in t_indices:
                                group_nodes[t_ind] = [token, targ_feats, feat_index]
                            self.cache[cache_key] = (token, tnode_index, t_indices, None, targ_feats)
                            
                tnode_index += 1
                        
        # Make indices for tgroup trees
        for src_index in self.tree:
            if src_index in node_index_map:
                self.ttree.add(node_index_map[src_index])
        # Add TNode elements
        tgnode_elements = []
        tginst, tnodes, agr, tgnodes = top_group_attribs
        if agr:
            agreements[tginst] = agr
            if verbosity > 1:
                print(" build(): tginst {} agr {}, agreements {}".format(tginst, agr, agreements))
        subtnodes = tg_tnodes[1] if len(tg_tnodes) > 1 else []
        self.add_tnodes(tnodes, subtnodes, tginst, group_nodes, node_features)
        # Store local variables as instance variables
        self.node_features = node_features
        self.group_nodes = group_nodes
        self.agreements = agreements
        return True

    def add_tnodes(self, tnodes, subtnodes, tginst, group_nodes, node_features):
        """Incorporate TNodes into nodes and features of TTrans."""
        for tnode in tnodes:
            features = tnode.features or FeatStruct({})
            src_index = len(node_features)
            self.ttree.add(src_index)
            index = [(tginst, tnode.index)]
            feat_index = len(node_features)
            node_features.append([tnode.token, features, index])
            group_nodes[index[0]] = [tnode.token, features, feat_index]
        # TNodes in subTTs
        for tnode in subtnodes:
            features = tnode.features or FeatStruct({})
            src_index = len(node_features)
            self.ttree.add(src_index)
            index = [(tnode.group, tnode.index)]
            feat_index = len(node_features)
            node_features.append([tnode.token, features, index])
            

    @staticmethod
    def get_root_POS(token):
        """Token may be something like guata_, guata_v, Ty_q_v."""
        if Entry.is_special(token) or '_' not in token:
            return token, None
        root, x, pos = token.rpartition("_")
        if pos not in ['v', 'a', 'n']: # other POS categories possible?
            # the '_' is part of the word itself
            return token, None
        return root, pos

    @staticmethod
    def merge_agrs(agr_list):
        """Merge agr dicts in agr_list into a single agr dict."""
#        print("  Merging agreements for merged nodes {}".format(agr_list))
        result = {}
        for agr in agr_list:
            if not agr:
                continue
            for k, v in agr:
                if k in result:
                    if result[k] != v:
                        print("Warning: agrs in {} failed to merge; {} and {} don't match".format(agr_list, result[k], v))
                        return 'fail'
                    else:
                        continue
                else:
                    result[k] = v
#        print("  Result", result)
        return result

    def generate_words(self, verbosity=0):
        """Do inter-group agreement constraints, and generate wordforms for each target node."""
        # Reinitialize nodes
#        print("Generating words in {}, features {}".format(self, self.node_features))
        self.nodes = []
        for group, agr_constraints in self.agreements.items():
#            print("Group {}, agr constraints {}".format(group, agr_constraints))
            for agr_constraint in agr_constraints:
                i1, i2 = agr_constraint[0], agr_constraint[1]
                feature_pairs = agr_constraint[2:]
                # Find the sentence nodes for the agreeing group nodes in the group_nodes dict
                agr_node1 = self.group_nodes[(group, i1)]
                agr_node2 = self.group_nodes[(group, i2)]
#                print("Found node1 {} and node2 {} for constraint {}".format(agr_node1, agr_node2, feature_pairs))
                agr_feats1, agr_feats2 = agr_node1[1], agr_node2[1]
                feat_index1, feat_index2 = agr_node1[2], agr_node2[2]
                # FSSets agr_feats1 and agr_feats2 have to be unfrozen before they can be made to agree
                if isinstance(agr_feats1, FeatStruct):
                    agr_feats1 = FSSet(agr_feats1)
                if isinstance(agr_feats2, FeatStruct):
                    agr_feats2 = FSSet(agr_feats2)
                agr_feats1 = agr_feats1.unfreeze(cast=False)
                agr_feats2 = agr_feats2.unfreeze(cast=False)
                af1, af2 = FSSet.mutual_agree(agr_feats1, agr_feats2, feature_pairs)
                # Replace the frozen FSSets with the modified unfrozen ones
#                print("Modified FSSets: {}, {}".format(af1, af2))
                agr_node1[1], agr_node2[1] = af1, af2
                self.node_features[feat_index1][1] = af1
                self.node_features[feat_index2][1] = af2
        generator = self.sentence.target.generate
#        print("Features for generation: {}".format(self.node_features))
        for token, features, index in self.node_features:
            root, pos = TreeTrans.get_root_POS(token)
            if verbosity:
                print("  Token {}, features {}, index {}, root {}, pos {}".format(token, features.__repr__(), index, root, pos))
            output = [token]
            if not pos:
                # This word doesn't require generation, just postprocess and return it in a list
#                print("Generating {}: {}".format(index, output))
                if self.target.postsyll:
                    token = self.target.syll_postproc(token)
                    output = [token]
                self.nodes.append((output, index))
            else:
#                print("Generating {} : {} : {}".format(root, features.__repr__(), pos))
                output = generator(root, features, pos=pos)
                self.nodes.append((output, index))
            if verbosity:
                print("Generating target node {}: {}".format(index, output))
#        print("nodes after generation: {}".format(self.nodes))

    def make_order_pairs(self, verbosity=0):
        """Convert group/index pairs to integer (index) order pairs.
        Constrain order in merged groups."""
        # Reinitialize order pairs
        self.order_pairs.clear()
        if verbosity:
            print("ORDERING pairs for {}".format(self))
            print(" mergers {}, nodes {}".format(self.mergers, self.nodes))
        tgroup_dict = {}
        for index, (forms, constraints) in enumerate(self.nodes):
#            print("Order pairs for node {} with forms {} and constraints {}".format(index, forms, constraints))
#            print("Constraints {} for tdict {}".format(index, constraints))
            for tgroup, tg_index in constraints:
                if tgroup not in tgroup_dict:
                    tgroup_dict[tgroup] = []
                tgroup_dict[tgroup].append((index, tg_index))
#        print("tgroup_dict {}".format(tgroup_dict))
        for pairs in tgroup_dict.values():
            for pairpair in itertools.combinations(pairs, 2):
                pairpair = list(pairpair)
                # Sort by the target index
                pairpair.sort(key=lambda x: x[1])
                self.order_pairs.append([x[0] for x in pairpair])
        # Order nodes within merged groups
        for node, (inner, outer) in self.mergers:
            if verbosity:
                print("  Merger: tnode index {}, inner group {}, outer group {}".format(node, inner, outer))
            # node is sentence node index; inner and outer are groups
            # Indices (input, tgroup) in inner and outer groups
            inner_nodes = tgroup_dict[inner]
            outer_nodes = tgroup_dict[outer]
            # Get the tgroup index for the merge node
            merge_tg_i = dict(outer_nodes)[node]
            # Get input indices for outer group's units before and after the merged node
            prec_outer = [n for n, i in outer_nodes if i < merge_tg_i]
            foll_outer = [n for n, i in outer_nodes if i > merge_tg_i]
            if prec_outer or foll_outer:
                # Get input indices for inner group nodes other than the merge node
                other_inner = [n for n, i in inner_nodes if n != node]
                # Each outer group node before the merge node must precede all inner group nodes,
                # and each outer group node after the merge node must follow all inner group nodes.
                # Add order pair constraints (using input indices) for these constraints.
                for o in prec_outer:
                    for i in other_inner:
                        self.order_pairs.append([o, i])
                for o in foll_outer:
                    for i in other_inner:
                        self.order_pairs.append([i, o])
        if verbosity:
            print('  Order pairs: {}'.format(self.order_pairs))

    def svar(self, name, lower, upper, lower_card=0, upper_card=MAX, ess=True):
        return Var(name, lower, upper, lower_card, upper_card,
                   essential=ess, rootDS=self.dstore)

    def create_variables(self, verbosity=0):
        """Create an order IVar for each translation node and variables for each group tree."""
        # Reinitialize variables
        self.variables.clear()
        nnodes = len(self.nodes)
#        print("Creating variables: nnodes {}, order pairs {}".format(nnodes, self.order_pairs))
        self.variables['order_pairs'] = DetVar("order_pairs", set([tuple(positions) for positions in self.order_pairs]))
        self.variables['order'] = [IVar("o{}".format(i), set(range(nnodes)), rootDS=self.dstore, essential=True) for i in range(nnodes)]
#        # target-language trees
#        self.variables['tree_sindices'] = []
#        self.variables['trees'] = []
#        for i, t in enumerate(self.trees):
#            if len(t) > 1:
#                # Only make a variable if the tree has more than one node.
#                self.variables['tree_sindices'].append(DetVar("tree{}_sindices".format(i), set(t)))
#                self.variables['trees'].append(self.svar("tree{}".format(i), set(), set(range(nnodes)), len(t), len(t), ess=False))

    def create_constraints(self, verbosity=0):
        """Make order and disjunction constraints."""
        # Reinitialize constraints
        self.constraints.clear()
        if verbosity:
            print("Creating constraints for {}".format(self))
        ## Order constraints
        order_vars = self.variables['order']
        self.constraints.append(PrecedenceSelection(self.variables['order_pairs'], order_vars))
        self.constraints.append(Order(order_vars))
#        ## Tree constraints
#        for i_var, tree in zip(self.variables['tree_sindices'], self.variables['trees']):
#            self.constraints.append(UnionSelection(tree, i_var, order_vars))
#            # Convexity (projectivity)
#            self.constraints.append(SetConvexity(tree))

    def realize(self, verbosity=0, display=False, all_trans=False, interactive=False):
        """Run constraint satisfaction on the order and disjunction constraints,
        and convert variable values to sentence positions."""
#        print("Realizing {}".format(self))
        generator = self.solver.generator(test_verbosity=verbosity, expand_verbosity=verbosity)
        try:
            proceed = True
            while proceed:
                # Run solver to find positions (values of 'order' variables)
                succeeding_state = next(generator)
                order_vars = self.variables['order']
                positions = [list(v.get_value(dstore=succeeding_state.dstore))[0] for v in order_vars]
#                print("Found positions {}".format(positions))
                # list of (form, position) pairs; sort by position
                node_pos = list(zip([n[0] for n in self.nodes], positions))
                node_pos.sort(key=lambda x: x[1])
                # just the form
                output = [n[0] for n in node_pos]
                self.outputs.append(output)
                self.output_strings.append(TreeTrans.output_string(output))
                if display:
                    self.display(len(self.outputs)-1)
                if verbosity:
                    print('FOUND REALIZATION {}'.format(self.outputs[-1]))
                if all_trans:
                    continue
                if not interactive or not input('SEARCH FOR ANOTHER REALIZATION FOR TRANSLATION {}? [yes/NO] '.format(self)):
                    proceed = False
        except StopIteration:
            if verbosity:
                print('No more realizations for translation')
