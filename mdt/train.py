# Mainumby. Parsing and translation with minimal dependency grammars.
#
########################################################################
#
#   This file is part of the Mainumby project within the PLoGS metaproject
#   for parsing, generation, translation, and computer-assisted
#   human translation.
#
#   Copyleft 2017; PLoGS <gasser@indiana.edu>
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

# This eventually loads ui, segment, record, cs, utils, language, entry
# some morphology functions (more needed?)
from .sentence import *

class Trainer:
    """Take a bilingual Document and the two associated languages, and learn
    new groups based on current groups."""

    # Maximum number of solutions to find for source sentences
    max_sols=3

    def __init__(self, doc, verbose=False):
        self.doc = doc
        self.source = doc.language
        self.target = doc.target

    def __repr__(self):
        return "T[{}]T".format(self.doc.id)

    def initialize(self):
        # Initialize sentences if they're not already
        if not doc.initialized:
            doc.initialize()

    def train1(self, index=-1, srcsent=None, targsent=None):
        """Process a sentence pair. Assumes both sentences have been initialized."""
        if index >= 0:
            srcsent, targsent = self.doc.get_sentence_pair(index)
        # Groups found in target language initialization
        targginsts = targsent.groups
        targgroups = [gi.group for gi in targginsts]
        print("Target groups: {}".format(targgroups))
        # First find all solutions for the source sentence
        srcsent.solve(translate=True, all_sols=True, max_sols=Trainer.max_sols)
        soltgroups = []
        for solution in srcsent.solutions:
            print("Checking solution {}".format(solution))
            tgroups = []
            for ginst, snodes in zip(solution.ginsts, solution.trees):
                print("  Checking ginst {} with snodes {}".format(ginst, snodes))
                for tgroup, gnodes, tnodes in ginst.translations:
                    # Check whether tgroup is among groups found during target initialization
                    # (tgroup is a Group instance, target sentence groups are GInst instances)
                    if tgroup in targgroups:
                        print("    Found solution tgroup {} in target sentence groups".format(tgroup))
                        tgroups.append(tgroup)
            soltgroups.append(tgroups)
        for i, sg in enumerate(soltgroups):
            print("Tgroups for solutions {}: {}".format(i, sg))

    def get_target_roots(self, tsent):
        """Get a list of token, root set pairs from the analysis of target sentence tsent."""
        return [(a[0], set([aa['root'] for aa in a[1]])) for a in tsent.analyses]

    def get_target_tokens(self, tsent):
        """Set of all tokens in target sentence."""
        return {a[0] for a in self.get_target_roots(tsent)}

    def get_source_trans_roots(self, ssent):
        """Return lists giving target tokens, roots, etc. for each solution of the source sentence."""
        solroots = []
        if not ssent.solutions:
            ssent.solve(translate=True, all_sols=True, max_sols=Trainer.max_sols)
        for solution in ssent.solutions:
            solroots1 = []
            for ginst in solution.ginsts:
                solroots2 = []
                tt = ginst.treetrans
#                subtt = tt.subTTs
#                if subtt:
#                    print("TT {} has subtrees {}".format(tt, subtt))
                translations = ginst.translations
                output_strings = tt.output_strings
                if not output_strings:
                    output_strings = [None] * len(translations)
                for out, (group, words, x) in zip(output_strings, translations):
                    solroots2.append((out, [(root, feats, position) for g, root, feats, agr, position in words]))
                solroots1.append(solroots2)
            solroots.append(solroots1)
        return solroots

    def get_source_trans_tokens(self, ssent):
        """Return the tokens in the translations for all solutions of the source sentence."""
        root_lists = self.get_source_trans_roots(ssent)
        tokens = []
        for solution in root_lists:
            sol_tokens = []
            for sollist in solution:
                for tokenlist in sollist:
                    token = tokenlist[0]
                    if token:
                        if ' ' in token:
                            token = token.split('|')
                            for t in token:
                                if " " in t:
                                    sol_tokens.extend(t.split())
                                else:
                                    sol_tokens.append(t)
                        elif '|' in token:
                            sol_tokens.extend(token.split('|'))
                        else:
                            sol_tokens.append(token)
            tokens.append(sol_tokens)
        return tokens

    def compare_tokens(self, index=-1, ss=None, ts=None):
        """For each source sentence solution, return the tokens overlapping with the target sentence."""
        if not ss or not ts:
            ss, ts = self.doc.get_sentence_pair(index)
        soltokens = self.get_source_trans_tokens(ss)
        ttokens = self.get_target_tokens(ts)
        return [ttokens.intersection(st) for st in soltokens]

    def compare_roots(self, index=-1, ss=None, ts=None):
        """For each source sentence solution, return the roots overlapping with the target sentence."""
        if not ss or not ts:
            ss, ts = self.doc.get_sentence_pair(index)
        solroots = self.get_source_trans_roots(ss)
        troots = self.get_target_roots(ts)
        troots_coll = set()
        for tr1 in troots:
            troots_coll.update(tr1[1])
        solroots_coll = []
        for sr in solroots:
            # One solution's tokens and roots
            sr0 = set()
            for ssr in sr:
                for srrr in ssr:
                    rr = srrr[1]
                    for rrr in rr:
#                        print("RRR {}".format(rrr))
                        root = rrr[0]
                        if '$' not in root:
                            sr0.add(root)
            solroots_coll.append(sr0)
        st_root_inters = [s.intersection(troots_coll) for s in solroots_coll]
        return solroots_coll, troots_coll, st_root_inters

    def align(self, index=-1, ss=None, ts=None, sol=None):
        if not ss or not ts:
            ss, ts = self.doc.get_sentence_pair(index)
        if not sol and not ss.solutions:
            # Get one solution
            ss.solve(translate=True)
            sol = ss.solutions[0]
        tsanals = ts.analyses
        tto = sol.get_ttrans_outputs()
        for indices, outputs, gname, mergers in tto:
            stokens = [ss.tokens[x] for x in indices]
            print("TOKENS {}||{}, outputs {}, gname {}".format(stokens, indices, outputs, gname))

#    def match_ttrans(self, tt_props, 
        
        
