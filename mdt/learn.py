#   
#   Mainumby: bilingual corpora and patterns to search for in corpora.
#
########################################################################
#
#   This file is part of the HLTDI L^3 project
#   for parsing, generation, translation, and computer-assisted
#   human translation.
#
#   Copyright (C) 2014, HLTDI <gasser@indiana.edu>
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

# 2014.07.04
# -- Created
#    Possible classes:
#    Pattern -- head (root or POS), dependent (root or POS);
#       relative position; gaps
#    Corpus -- list (dict?) of sentences, consisting of lists
#       of word strings or word representations
# 2014.07.05-12
# -- Lots more stuff
#    Reading in corpora from L3-Morpho-analyzed files.
#    Returning sentences in corpora containing particular words or roots or grammatical features.
#    Patterns defined more clearly.
#    Matching patterns in corpora sentences.
#    Searching for sentences matching patterns in sentences.
# 2014.07-08
# -- Unsupervised disambiguation.
# 2014.08-09
# -- Disambiguation using tags from POS tagger.

# Need this to parse and interpret features

from mdt.morphology.fs import *
from .utils import *

class Corpus(list):
    """A list of sentences, each a tuple of words or word-representation FeatStruct objects."""

    def __init__(self, name='', feat_order=None, tag_map=None):
        list.__init__(self)
        self.name = name or 'anon'
        # Store string->FeatStruct mapping here to save time in reading in corpus
        self.feat_cache = {}
        self.feat_order = feat_order or {}
        # Dict of frequencies of different grams for particular POSs (see count_grams()).
        self.pos_grams = {}
        # List of ambig words and their analyses
        self.ambiguous = []
        # Dict of disambiguated words, with analyses ordered by frequency
        self.disambiguated = {}
        # Dict mapping POS tags to feats
        self.tag_map = tag_map or {}

    def add_feat_order(self, feat, vals):
        """Create an explicit likelihood ordering of values for a particular feature."""
        self.feat_order[feat] = vals

    def read(self, file, lines=0, expand=True, tag_ambig=True):
        """Extend the corpus with a list of lists of word-analysis strings.
        anl_file is a sentence-by-line file with words analyzed by L3Morpho anal_file()
        with minim=True. If expand is True, word analyses are expanded into dicts.
        tag_file is a sentence-by-line of word_tag strings."""
        anl_file = file + '.anl'
        tag_file = file + '.tg'
        print("Reading corpus from {}".format(anl_file))
        t = open(tag_file, encoding='utf8')
        a = open(anl_file, encoding='utf8')
        n = 0
        for tag_line, anl_line in zip(t, a):
            tags = tag_line.split()
            words = anl_line.split()
            if lines and n >= lines:
                return
            n += 1
            if n % 50000 == 0:
                print("Read {} lines".format(n))
            sentence = []
            wi = 0
            tag_words = tag_line.split()
            # Get rid of spaces
            for tw in tag_words[:]:
                if tw[0] == '_' and tw[1] != '_':
                    tag_words.remove(tw)
            for word in anl_line.split():
                if word[0] == '(' and word[-1] == ')':
                    continue
                tagged = tag_words[wi]
                tword, x, tag = tagged.rpartition('_')
                tword = tword.lower()
#                print('Word {}, tword {}'.format(word, tword))
                if ';' in word and len(word) > 2:
                    form, analyses = word.split(';')
                    if tword != form:
                        print("Analyzed word {} doesn't match {}!".format(form, tword))
                        print('  Sentence {}'.format(tag_words))
                    w = [form, tag]
                    for analysis in analyses.split('|'):
                        anal_attribs = analysis.split(':')
                        root = anal_attribs[0]
                        pos = False
                        feats = False
                        if root == '*':
                            # Root is same as wordform, so don't record
                            root = False
                        if len(anal_attribs) > 2:
                            # There is an analysis FS string
                            # Create to make a FeatStruct object
                            fs = anal_attribs[2]
                            if fs == '[]':
                                fs1 = '['
                            else:
                                fs1 = fs[:-1] + ','
                            fs = fs1 + 'p=' + anal_attribs[1] + ']'
                            if fs in self.feat_cache:
                                feats = self.feat_cache[fs]
                            else:
                                feats = FeatStruct.from_string(fs)
                                self.feat_cache[fs] = feats
                            if tag_ambig and self.tag_map:
                                if not self.tag_disambig(tag, feats):
#                                    print("Feats {} in word {} doesn't match {}".format(feats, word, tag))
                                    continue
                        elif len(anal_attribs) == 2:
                            # POS but no additional grammatical constraints
                            pos = anal_attribs[1]
                            if pos in self.feat_cache:
                                feats = self.feat_cache[pos]
                            else:
                                feats = FeatStruct({'p': anal_attribs[1]})
                                self.feat_cache[pos] = feats
                            if tag_ambig and self.tag_map:
                                if not self.tag_disambig(tag, feats):
#                                    print("POS {} in word {} doesn't match {}".format(anal_attribs[1],
#                                                                                      word, tag))
                                    continue
                        w.extend([root, feats])
                    sentence.append(tuple(w))
                else:
                    if tword != word:
                        print("{} doesn't match {}!".format(word, tword))
                        print('  Sentence {}'.format(tag_words))
                    sentence.append((word, tag))
                wi += 1
            self.append(tuple(sentence))
#                    
#                if expand:
#                    for i, word in enumerate(words):
#                        if ';' in word:
#                            # There is an analysis of the word
#                            form, analyses = word.split(';')

    def __repr__(self):
        return "C~~{}".format(self.name)

    def tag_disambig(self, tag, anal, mapping=None):
        """Is anal consistent with tag, using mapping."""
        if not mapping:
            mapping = self.tag_map
        tag0 = tag[0]
        if tag0 in mapping:
            constraints = mapping[tag0]
            # First constraint is a single feat-value tuple
            # Remove all anals that don't match it
            constraint0 = constraints[0]
            feat, val = constraint0
            if feat not in anal or anal[feat] != val:
                return False
            if len(constraints) > 1:
                for constraint in constraints[1:]:
                    # CAR of constraint is range within tag
                    start, end = constraint[0]
                    tag1 = tag[start:end]
                    if tag1 in constraint[1]:
                        fvs = constraint[1][tag1]
                        for feat, val in fvs:
                            if feat not in anal or anal[feat] != val:
                                return False
        else:
            if 'p' not in anal or anal['p'] != tag0:
                return False
        return True
            
    @staticmethod
    def words(seq):
        """Return the word form in the sequence or sentence items."""
        return [w if isinstance(w, str) else w[0] for w in seq]

    @staticmethod
    def get_root(word, word_tup):
        if isinstance(word_tup, str):
            return None
        root = word_tup[0]
        if not root:
            return word
        return root

    @staticmethod
    def get_pos(word_tup):
        gram = word_tup[1]
        if gram:
            return gram.get('p', False)
        return False

    @staticmethod
    def get_gram(word_tup):
        return word_tup[1]

    @staticmethod
    def get_form_anals(word, corpus=None):
        """word is a string (form) or a tuple consisting of form following by
        unsegmented pairs representing analyses. Return a tuple consisting of the
        wordform followed by pairs (root, features) representing analyses.
        With corpus argument, use ordering information in corpus dicts.
        """
        if isinstance(word, str):
            return word, ()
        else:
            form = word[0]
            tag = word[1]
            anals = [list(word[i+2:i+4]) for i in range(0, len(word)-2, 2)]
            if corpus:
                corpus.order_anals(form, anals)
            # Replace False root with form
            for index, (root, gram) in enumerate(anals):
                if not root:
                    anals[index][0] = form
            return form, anals

    def get_gram_freq(self, gram):
        """Assign an integer to gram on the basis of the explicit order of feature values
        in the feat_order dict."""
        val = 0
        if gram:
            # Analyses with no grammar (unanalyzed) are preferred
            val += 1
            for feat, value in gram.items():
                if feat in self.feat_order:
                    values = self.feat_order[feat]
                    if value in values:
                        val += values.index(value)
        return val

    def order_anals(self, form, anals):
        """Order analyses by the likelihood of particular feature-values in the gram FeatStruct.
        Each anal is (root, gram)."""
        if len(anals) > 1:
            print("Ambiguity!", form, anals)
        anals.sort(key=lambda x: self.get_gram_freq(x[1]))

    def set_pos_grams(self, pos, roots):
        """Make an entry in the corpus's pos_grams dict for pos by counting
        occurrences of different grams for roots."""
        d = self.count_grams(roots, pos=pos, sort=False, disambig=False)
        self.pos_grams[pos] = d

    def count_grams(self, roots, pos='', all_anals=False, sort=True, disambig=False, verbose=False):
        """Return a dict or a sorted list of grammatical features of a set of roots by their frequency.
        If disambig is True or a POS, separate out analyses that have that POS as well
        as the target POS (pos option)."""
        if isinstance(roots, str):
            roots = [roots]
        d = {}
        if disambig:
            dis = {}
        forms = []
        # There can be only one of these
        allroots = set()
        for i, sent in enumerate(self):
            if (i+1) % 50000 == 0:
                print("Counted grams for {} roots in {} sentences".format(pos, i+1))
            for w in sent:
                form, anals = Corpus.get_form_anals(w, corpus=self)
                if anals:
                    if disambig and len(anals) > 1:
                        wroots = [a[0] for a in anals]
                        wgrams = [a[1] for a in anals]
                        if any([(not w) for w in wgrams]):
                            continue
#                        print('form {}, anals {}'.format(form, anals))
                        poss = [g.get('p', '') for g in wgrams]
                        if any([(r in roots and p == pos) for r, p in zip(wroots, poss)]) and disambig in poss:
#                        if any([r in roots for r in wroots]):
#                            if pos in poss and disambig in poss:
                            p_tup = None
                            d_tup = None
                            for r, g in anals:
                                p = g.get('p')
                                if p == pos and not p_tup:
                                    p_tup = g
                                    allroots.add(r)
                                elif p == disambig:
                                    d_tup = g
                                    allroots.add(r)
                                if p_tup and d_tup:
                                    break
                            tups = (p_tup.to_tuple(), (r, d_tup.to_tuple()))
                            if tups in dis:
                                dis[tups] += 1
                            else:
                                dis[tups] = 1
                        continue
#                    nanals = len(anals)
#                    nanals = 0
                    for wroot, gram in anals:
                        if wroot in roots:
#                            if verbose:
#                                print("Unambiguous instance of {}: {}".format(form, anals))
                            p = gram.get('p', '')
                            if p != pos:
                                continue
#                            incr = 1 / nanals
                            t = gram.to_tuple()
                            if t in d:
                                d[t] += 1
                            else:
                                d[t] = 1
                                forms.append((form, t))
                            # Only include the first (presumably most frequent)
                            # grammatical features
                            break
        if disambig:
#            if verbose:
#                print("All roots: {}".format(allroots))
            return d, dis
#, forms
        s = sum([c for c in d.values()])
        for f, c in d.items():
            d[f] = c / s
        if sort:
            l = list(d.items())
            l.sort(key=lambda x: x[1], reverse=True)
            return l
        return d

    def count_roots(self, roots, sort=True):
        """Return either a dict or a sorted list of roots by their frequency."""
        d = {}
        constraint = (None, (roots, None))
        for sent in self:
            for w in sent:
                # Match on analyses sorted by within-POS feature freq
                match = Pattern.match_item(w, constraint, corpus=self)
                if match:
                    root = match[0]
                    if root in d:
                        d[root] += 1
                    else:
                        d[root] = 1
                    # Don't bother to look for another match with this word
                    continue
        if sort:
            # Sort by frequency
            l = list(d.items())
            l.sort(key=lambda x: x[1], reverse=True)
            return l
        else:
            return d

    def segments(self, indices):
        """Return all segments in sentences indexed by indices,
        a list of tuples of the form (sent_index, (start_word_index, end_word_index+1)).
        """
        return [self[s][w0:w1] for s, (w0, w1) in indices]

    def sents(self, constraints=(None, None)):
        """Find all sentences containing word with features matching feats if any.
        constraints is (forms, (root, gram))
        forms is a set of wordforms.
        root is None or a string or a set of strings.
        feats is None or a list/tuple of feat-val constraint tuples.
        Return list of pairs of sentence indices and word indices with sentences."""
        result = []
        for sindex, sent in enumerate(self):
            indices = []
            for index, w in enumerate(sent):
                if Pattern.match_item(w, constraints, corpus=self):
                    indices.append(index)
            if indices:
                result.append((sindex, indices))
        return result

    def set_ambig(self, pos=True):
        """Find a list of all ambiguous words in the corpus
        with their occurrences. If pos is True, return only
        words with POS ambiguity."""
        print("Finding ambiguous words")
        results = {}
        for sindex, sent in enumerate(self):
            indices = []
            for index, w in enumerate(sent):
                if isinstance(w, tuple) and len(w) > 3:
                    form = w[0]
                    if form in results:
#                        print('Form {} in results'.format(form))
                        results[form][1] += 1
                        continue
                    form, anals = Corpus.get_form_anals(w, corpus=self)
                    results[form] = [anals, 1]
#                    # w has more than one analysis
#                    if pos:
#                        if not all([a[1] for a in anals]):
#                            continue
#                        if len({a[1]['p'] for a in anals}) < 2:
#                            # Different POSs
#                            continue
        results = list(results.items())
        results.sort(key=lambda x: x[1][1], reverse=True)
        self.ambiguous = results

    def disambiguate_all(self, verbose=False):
        """Disambiguate saved ambiguous words, reordering analyses."""
        for a in self.ambiguous:
            disamb = self.disambiguate(a, verbose=verbose)
            if not disamb:
                continue
            pos1, pos2 = disamb

    def disambiguate(self, word, verbose=False):
        """Two kinds of evidence for disambiguation.
        self.pos_grams gives relative frequencies of different grams
        for particular POSs.
        self.count_grams() counts the occurrences of different grams
        for the *roots* associated with each interpretation, separating
        unambiguous from ambiguous instances of the roots.
        """
        form, (analyses, count) = word
        if verbose:
            print("Attempting to disambiguate {}".format(form))
        roots = {}
        feats = {}
        root_set = set()
        for analysis in analyses:
            root, anal = analysis
            if not anal:
                return analysis
            pos = anal.get('p')
            anal_tup = anal.to_tuple()
            feats[pos] = anal_tup
            if pos in roots:
                roots[pos].add(root)
            else:
                roots[pos] = {root}
            root_set.add(root)
        poss = list(roots.keys())
        if len(poss) > 2:
            if verbose:
                print("{} is 3-way POS-ambiguous".format(form))
            return False
        elif len(poss) == 1:
            if verbose:
                print("{} is not POS-ambiguous".format(form))
            return False
        p1, p2 = poss
        expected = {}
        ambig_counts = {}
        for p, r in roots.items():
            if p == p1:
                p_o = p2
            else:
                p_o = p1
            c = self.count_grams(r, pos=p, disambig=p_o)
            pos_grams = self.pos_grams[p]
            # pcount: counts of unambiguous forms of the root
            # outcount: counts of ambiguous forms of the root
            pcount, outcount = c
            # expected freq of features of ambiguous forms
            outfeats = [f[0] for f in outcount.keys()]
            # total freq of ambiguous forms
            outfreq = sum([pos_grams[f] for f in outfeats])
            featfreq = pos_grams[feats[p]]
#            print('pcount {}, outcount {}, outfreq {}, featfreq {}'.format(pcount, outcount, outfreq, featfreq))
            # Check to see whether there are unambiguous instances corresponding to ambiguous ones
            # for example, serlo for ser (same grammatical features)
            for infeats, outfeats in outcount.keys():
                if infeats in pcount:
                    if verbose:
                        print("Both ambiguous and unambiguous {}".format(infeats))
                    outcount[(infeats, outfeats)] += pcount[infeats]
                    del pcount[infeats]
            if pcount:
                # there are at least some unambiguous forms of the root.
                # total of their counts:
                psum = sum([v for v in pcount.values()])
                if any([f not in pos_grams for f in pcount.keys()]):
                    return False
                exp_unamb = sum([pos_grams[f] for f in pcount.keys()])
                if verbose:
                    fstring = 'Count of unamb feats for {}: {}; expected freq of amb feats {}, expected freq of unamb feats {}'
                    print(fstring.format(r, psum, outfreq, exp_unamb))
                exp = (psum * outfreq) / exp_unamb
                if verbose:
                    print('Expected count of ambiguous {} analyses with root {}: {}'.format(p, r, exp))
                exp = round((featfreq * exp) / outfreq)
                if verbose:
                    print('  Expected count of {} analysis: {}'.format(feats[p], exp))
                expected[p] = exp
            else:
                if verbose:
                    print("No unambig {} forms of {}".format(p, r))
                ambig_counts[p] = []
                tot = sum([c for c in outcount.values()])
                other_pos = None
                other = []
                for (inpos, outpos), c in outcount.items():
                    r, f = outpos
                    if r not in root_set:
                        if verbose:
                            print("root {} is not in root list {}".format(r, roots))
                        # Don't bother trying if there are more than two roots
                        return False
                    other_pos = dict(f)['p']
                    exp_other = self.pos_grams[other_pos][f]
                    ambig_counts[p].append((inpos, outpos, other_pos, c / tot, exp_other))

        if expected:
            diffs = []
            ratios = []
            for p, c in expected.items():
                diff = abs(count - c)
                if not count or not c:
                    rat = 0.0
                else:
                    rat = min(c / count, count / c)
                if verbose:
                    print("POS {}".format(p))
                    s = "  Actual count: {}, expected count: {}; difference from actual: {}, exp/act ratio {}"
                    print(s.format(count, c, diff, round(rat, 5)))
                diffs.append((p, diff))
                ratios.append((p, rat))
            if len(diffs) == 2:
                if diffs[0][1] < diffs[1][1]:
                    print("{} preferred by diffs ({} vs. {})".format(diffs[0][0], diffs[0][1], diffs[1][1]))
                else:
                    print("{} preferred by diffs ({} vs. {})".format(diffs[1][0], diffs[1][1], diffs[0][1]))
                if ratios[0][1] > ratios[1][1]:
                    print("{} preferred by ratios ({} vs. {})".format(diffs[0][0], ratios[0][1], ratios[1][1]))
                    return diffs[0][0], diffs[1][0]
                else:
                    print("{} preferred by ratios ({} vs. {})".format(diffs[1][0], ratios[1][1], ratios[0][1]))
                    return diffs[1][0], diffs[0][0]
        if ambig_counts:
            # What to do if one or both of the alternatives has only ambiguous morphological variants, for example,
            # debate as noun: debate (n: sing. / v: 3s pres.), debates (n: plur. / v: 2s pres.)
            scores = {}
            for pos, counts in ambig_counts.items():
                if verbose:
                    print("POS {}".format(pos))
                scores[pos] = 0
                corp_counts = self.pos_grams[pos]
                corp_count_sum = sum([corp_counts[c[0]] for c in counts])
                outtot = sum([x[4] for x in counts])
                for inf, outf, outpos, c, outexp in counts:
                    cc = corp_counts[inf]
                    # Should really be the proportion of the actually occurring features
                    cc = cc / corp_count_sum
                    c = round(c, 5); cc = round(cc, 5)
                    outexpprop = round(outexp / outtot, 5)
                    outdiff = c - outexpprop
                    outscore = round(outdiff * outdiff, 5)
                    indiff = c - cc
                    inscore = round(indiff * indiff, 5)
                    scores[pos] += inscore
                    if outpos in scores:
                        scores[outpos] += outscore
                    else:
                        scores[outpos] = outscore
                    if verbose:
#                        print('  Sum of in expected {}'.format(corp_count_sum))
                        s = "  {} / {} | {}: proportion of ambig {}, in expected proportion {}, out expected proportion {}"
                        print(s.format(FeatStruct.ppftup(inf), outf[0], FeatStruct.ppftup(outf[1]), c, cc, outexpprop))
            if verbose:
                print("Comparison: {}".format(scores))
            if len(scores) == 2:
                scores = list(scores.items())
                if scores[0][1] < scores[1][1]:
                    print("{} ({}) preferred over {} ({}) by comparing features for POSs".format(scores[0][0], scores[0][1],
                                                                                                 scores[1][0], scores[1][1]))
                    return scores[0][0], scores[1][0]
                elif scores[1][1] < scores[0][1]:
                    print("{} ({}) preferred over {} ({}) by comparing features for POSs".format(scores[1][0], scores[1][1],
                                                                                                 scores[0][0], scores[0][1]))
                    return scores[1][0], scores[0][0]

        return False

class Pattern(list):
    """A list of items to look for in sentences.
    Each list element is either a pair specifying constraints on words
    ({set of word forms}, ({set of roots}, (tuple of grammatical constraints)}}
    or a pair specifying bounds on a gap between words in the pattern.
    Any of the three components may be None.
    A further possibility, only for word forms, is a pair (tuple) with 'not' or '~'
    as the first element, meaning the word must *not* be a member of the set that
    is the second element of the pair.
    Abbreviated formats are possible; these are expanded during initialization; see complete().
    """

    def __init__(self, lst):
        list.__init__(self, lst)
        self.complete()

    def __repr__(self):
        return "&{}".format(list.__repr__(self))

    @staticmethod
    def is_gap(item):
        return isinstance(item, int) or (isinstance(item, tuple) and isinstance(item[0], int))

    @staticmethod
    def is_not(item):
        return isinstance(item, tuple) and item[0] in {"not", "~", "^"}

    def complete(self):
        """Expand incomplete items."""
        for index, item in enumerate(self):
            if isinstance(item, str):
                # A single form
                self[index] = ({item}, None)
            elif isinstance(item, set):
                item1 = list(item)[0]
                if isinstance(item1, str):
                    # A set of forms
                    self[index] = (item, None)
                elif isinstance(item1, tuple):
                    # A set of feature-value constraints
                    self[index] = (None, (None, item))
            elif isinstance(item, tuple):
                if isinstance(item[1], str):
                    # A single root string
                    self[index] = (None, ({item[1]}, None))
                elif isinstance(item[1], set):
                    # A set of roots
                    self[index] = (None, (item[1], None))
            elif isinstance(item, int):
                # A gap constraint; take this to be the upper bound
                self[index] = (0, item)

    @staticmethod
    def match_item(s_word, constraint=(None, None), corpus=None):
        """Does word from sentence match various constraints?
        Either the form should match or one or more other constraints
        must."""
        s_form, s_anals = Corpus.get_form_anals(s_word, corpus=corpus)
        forms, rg = constraint
        if forms:
            if isinstance(forms, tuple):
                # Negative; succeed if the word is not in the set
                # (which is the last element of the tuple)
                if s_form not in forms[-1]:
                    return s_form
            elif s_form in forms:
                return s_form
        else:
            for s_rg in s_anals:
                if Pattern.match_constraints(s_rg, rg):
                    return s_rg
        return None

    def match_gap(bounds=(0, 1), current=0):
        lower, upper = bounds
        if lower <= current <= upper:
            return True
        else:
            return False

    @staticmethod
    def match_constraints(w_rg, p_rg):
        """Does a pair of word properties (root, grammatical features/POS)
        match the corresponding constraints (if any) from a pattern?
        Pattern root constraint is a string or a set of root strings."""
        roots, grams = zip(w_rg, p_rg)
        wr, pr = roots
        if isinstance(pr, str):
            pr = {pr}
        if isinstance(pr, tuple):
            # word root should *not* be in pattern root set
            if wr in pr[-1]:
                return False
        elif pr and wr not in pr:
            # Either there is no pattern root constraint or the
            # roots must be equal
            return False
        wg, pg = grams
        if pg and wg and not wg.match_list(pg):
            # Either there is no list of feature pair constraints in
            # the pattern or the word has no grammatical FS or the
            # word's FS must match the feature pair list
            return False
        return True

    def match(self, sentence, corpus=None, verbose=True):
        """Does the Pattern match a sequence in the sentence?
        If so, return the boundary indices of matching words within the
        sentence."""
        p_index = 0
        p_item = self[0]
        s_start = 0
        gap = 0
        results = []
        s_index = 0
        while s_index < len(sentence):
            word = sentence[s_index]
            if verbose:
                print("Matching word {} against pitem {}".format(word, p_item))
#        for s_index, word in enumerate(sentence):
            if Pattern.is_gap(p_item):
                # First check to see whether the gap constraint is satisfied with the current gap
                if Pattern.match_gap(p_item, gap):
                    if verbose:
                        print("Gap pitem {} matches current gap {}".format(p_item, gap))
                    # Now see if we can move on to the next constraint with this word
                    next_p_item = self[p_index + 1]
                    if Pattern.match_item(word, next_p_item, corpus=corpus):
                        # Word matches constraint after the gap
                        if verbose:
                            print("Pitem after gap {} matches word #{}: {}".format(next_p_item, s_index, word))
                        # Finish with gap and next constraint
                        p_index += 2
                        if p_index >= len(self):
                            # We're done with the pattern
                            results.append((s_start, s_index + 1))
                            p_index=0;p_item=self[0];gap=0
                            s_index = s_start + 1
                        else:
                            # We're not done; there's another pattern element after the matched next one
                            p_item = self[p_index]
                            gap = 0
                            s_index += 1
                    else:
                        if verbose:
                            print("Pitem after gap fails to match word #{}: {}".format(s_index, word))
                        # Next pattern constraint fails to match this word; so increment the gap
                        # and go on to the next word
                        gap += 1
                        s_index += 1
                elif gap < p_item[0]:
                    if verbose:
                        print("Current gap {} is too short for pitem {}, skip current word".format(gap, p_item))
                    gap += 1
                    s_index += 1
                else:
                    if verbose:
                        print("Current gap {} is too long for gap pitem {}, starting over".format(p_item, gap))
                    # Outside the gap range, so fail on this attempt to match the pattern, and start over
                    p_index=0;p_item=self[0];gap=0
                    s_index = s_start + 1
            elif Pattern.match_item(word, p_item, corpus=corpus):
                if verbose:
                    print("{} matches pattern element {}: {}".format(word, p_index, p_item))
                if p_index == 0:
                    s_start = s_index
                p_index += 1
                if p_index == len(self):
                    # Done with pattern; return bounds (end is last index + 1)
                    results.append((s_start, s_index + 1))
                    p_index=0;p_item=self[0];gap=0
                    s_index = s_start + 1
                else:
                    # Not done, get next element
                    p_item = self[p_index]
                    s_index += 1
            elif p_index > 0:
                # Fail on this attempt; start over
                if verbose:
                    print("Fail on word {} middle of pattern".format(word))
                p_index=0;p_item=self[0];gap=0
                s_index = s_start + 1
            else:
                s_index += 1
        return results

    def search(self, corpus, segments=False, verbose=False):
        """Search a corpus for instances of this pattern,
        returning a list of their locations in the corpus or the sentence segments
        themselves, if segments is True."""
        results = []
        for index, sentence in enumerate(corpus):
            matched = self.match(sentence, verbose=verbose)
            if matched:
                for bounds in matched:
                    results.append((index, bounds))
        if segments:
            return c.segments(results)
        return results
