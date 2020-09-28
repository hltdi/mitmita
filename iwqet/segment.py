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
# 2020.09
# -- Updated generation to allow for cases where a single source POS
#    corresponds to multiple target POSs, e.g., Amh v -> Sgw vp, vi, vj

import itertools, copy, re
from .cs import *
from .morphology.semiring import FSSet
# needed for a few static methods
from .entry import Group, Token, JoinToken
from .record import SegRecord
from .utils import *
from iwqet.morphology.utils import reduce_lists

class Seg:
    """Interface class for segments:
    Segment, resulting from matching a group and possibly one or more merged groups under it
    SuperSeg, resulting from joining two or more Segments.
    """

    # Maximum number of generated forms permitted, given a root and set of update features
    max_gen_forms = 6

    # Maximum number of leaf Segments in Seg
    max_segments = 8

    # Maximum number of final strings for Segs
    max_final = 10

    # colors to display segments in interface
    tt_colors = ['blue', 'sienna', 'green', 'red', 'purple']

    tt_notrans_color = "Silver"

    color_index = 0

    special_re = re.compile("%[A-Z]+~")

    # Character indicating that tokens in translation string should be joined ("Carlos `-pe" -> "Carlos-pe")
    join_tok_char = "`"

    def __init__(self, segmentation):
        self.segmentation = segmentation
        self.sentence = segmentation.sentence
        self.source = segmentation.source
        self.target = segmentation.target
        self.segmentation = segmentation.sentence
        self.generated = False
        self.special = False
        # structure
        self.shead = None
        self.shead_index = -1
        self.thead = None
        self.scats = None
        self.depth = 1
        # source and target strings and features
        self.original_token_str = ''
        self.token_string = ''
        self.clean_trans = None
        # set during generation (no need to copy between Seg levels)
        self.morphology = None
        # set during finalization, using self.morphology
        self.final_morph = []
        # final translation string choices
        self.final = []
        # html
        self.html = []
        self.source_html = None
        # punctuation
        self.is_punc = False
        self.record = None
        self.gname = None
        self.indices = None

    def get_tokens(self):
        """Returns a set of all possible tokens for this segment."""
        toks = self.get_shead_tokens() or self.get_untrans_token() or [self.token_str]
        raw = self.get_shead_raw()
        if raw and raw not in toks:
            toks.append(raw)
        to_add = []
        for tok in toks:
            if '_' in tok:
                to_add.append(tok.split('_')[0])
        return set(toks + to_add)

    def get_untrans_token(self):
        """For untranslated segments, return the cleaned string."""
        return self.cleaned_trans and self.cleaned_trans[0][0]

    def count_segments(self):
        """Return the number of leaf Segments."""
        print("Warning: count_segments() not defined for this Seg instance.")

    ## Head properties (used in joining Segments to form Supersegs)

    def get_shead_raw(self):
        """The raw token for the source head."""
        if self.shead and self.shead_index >= 0:
            return self.tokens[self.shead_index]

    def get_shead_tokens(self):
        if self.shead:
            return [(h[0] if isinstance(h, tuple) else h) for h in self.shead]

    def get_shead_roots(self):
        if self.shead:
            return [h[0] for h in self.shead if isinstance(h, tuple)]

    def get_shead_feats(self):
        if self.shead:
            return [h[1] for h in self.shead if isinstance(h, tuple)]

    def get_shead_pos(self):
        if self.shead:
            pos = set()
            for h, f, p in self.shead:
                if p:
                    pos.add(p)
                if f and not isinstance(f, bool):
                    pos.add(f.get('pos'))
                elif '_' in h:
                    pos.add(h.split('_')[-1])
            return pos

    def get_thead_roots(self):
        if not self.generated:
            if self.thead:
                return [h[0] for h in self.thead]

    def get_thead_feats(self):
        if not self.generated:
            if self.thead:
                return [h[2] for h in self.thead]

    def get_thead_pos(self):
        if not self.generated:
            if self.thead:
                return [h[1] for h in self.thead]

    def generate(self, limit_forms=True, verbosity=0):
        raise NotImplementedError()

    def get_special(self, del_spec=False):
        """If Segment is special, return its category and the token as a tuple."""
        if self.special:
            if self.cleaned_trans:
                # Already translated
                token = self.get_shead_tokens()[0]
                pre, x, form = token.partition('~')
            else:
                tok = self.get_untrans_token()
                pre, form = tok.split('~')
            if del_spec:
                pre = pre[1:]
            return pre, form
        return None, None

    # Matching Join and Group instances

    def has_child(self):
        print("Error: has_child not defined for {}".format(self))

    def match_join(self, join_elem, join_pos, verbosity=0):
        """Does this Segment match a pattern element in a Join? join_elem
        is either a FSSet or a string."""
        if verbosity:
            print("  Matching item {} with join elem {} and pos {}".format(self, join_elem, join_pos))
        if join_pos:
            # If there's a POS for the join, it must be matched (there must also be a translation)
            if self.translation and JoinToken.match_pos(join_pos, self.get_shead_pos()):
                return True
            else:
                return False
        if isinstance(join_elem, str):
            # Match special type, category, or explicit token
            if Token.spec_char in join_elem:
                # Match special type
                pre, tok = self.get_special()
                return pre == join_elem and tok
            elif Token.cat_char in join_elem:
                # Match a category
                # This should fail SOMETIMES when there's no translation
                # DISTINGUISH THESE CASES WITH A CODE LIKE $$
                return self.scats and join_elem in self.scats
            else:
                toks = self.get_tokens()
                if verbosity > 1:
                    print("    Tokens to match {}".format(toks))
                return any([join_elem == tok for tok in toks]) and toks
        elif not self.translation:
            # If group element has features, matching segment must have translation
            return False
        else:
            feats = self.get_shead_feats()
            # Match features
            if feats:
                for feat in feats:
                    u = join_elem.u(feat, strict=True)
                    if u and u != 'fail':
                        return u
            return False

    def match_group_tok(self, group_tok, group_feats, verbosity=1):
        """Does this Seg match pattern elem and features from a Group?"""
        if verbosity:
            print(" Matching item {} with group token {}".format(self, group_tok))
        if Token.is_special(group_tok):
            if not self.special:
                return False
            pre = self.head_tok.prefix
            if verbosity:
                print(" Special prefix {}; group token {}".format(pre, group_tok))
                # Prefix could be more specific than group token, for example, %ND and %N
            if not pre.startswith(group_tok):
                return False
        else:
            groupcat = '$' in group_tok
            toks = self.get_tokens()
            feats = self.get_shead_feats()
#            print("Matching toks {}, feats {}, group feats {}".format(toks, self.get_shead_feats(), group_feats))
            # match tokens
            if groupcat:
                if not self.translation or (not self.scats or group_tok not in self.scats):
                    return False
            elif not any([group_tok == tok for tok in toks]) or isinstance(self, SuperSeg):
#                # Explicit string in group can't match a SuperSeg
                return False
#            if not any([group_tok == tok for tok in toks]) or isinstance(self, SuperSeg):
#                return False
            if not group_feats:
                # No group features to match so use head features if any
                if feats:
                    return feats[0] or True
                else:
                    return True
            elif feats:
                for feat in feats:
                    if verbosity:
                        print(" Matching group features {} with segment features {}".format(group_feats.__repr__(), feat.__repr__()))
                    # strict feature forces True feature in group_feats to be explicit in feat
                    # Be sure this is a FSSet
                    feat = FSSet(feat)
                    u = feat.u(group_feats, strict=True)
                    if u == 'fail':
                        return False
                    else:
#                        print("  result {}".format(u.__repr__()))
                        return u
        return True

    def get_group_cands(self, all_groups=None, verbosity=0):
        """Get groups that could match this segment and surrounding segments.
        Returns a set to prevent duplicates."""
        tokens = self.get_tokens()
        all_groups = all_groups or self.source.groups
        if all_groups and tokens:
            groups = set()
            for token in tokens:
                groups1 = all_groups.get(token)
                if groups1:
                    groups1 = [(g, g.head_index) for g in groups1]
                    groups.update(groups1)
            if verbosity and groups:
                print("  Found candidates {} for {}".format(groups, self))
            return groups

    def generate(self, limit_forms=True, verbosity=0):
        """Generate surface forms for segment."""
        if verbosity:
            print("Generating segment {} with cleaned trans {} and raw token str {}".format(self, self.cleaned_trans, self.raw_token_str))
        generator = self.target.generate
        mult_generator = self.target.mult_generate
        cleaned_trans = []; morphology = []
        for translation in self.cleaned_trans:
            output1 = []; morph = []
            if verbosity:
                print("  Generating {}".format(translation))
            for item in translation:
                if verbosity:
                    print("   Generating {}".format(item))
                if Token.is_special(item):
                    spec_trans = self.source.translate_special(item)
                    if spec_trans:
                        output1.append(Seg.clean_spec(spec_trans))
                        morph.append(None)
                    continue
                if isinstance(item, list):
                    if isinstance(item[0], list):
                        # multiple root, pos, feat combinations
                        # this can happen with Amh->Sgw for multiple verb 'POS's
#                        print("  Multiple root/POS/feats to generate")
                        root = item[0][0]
                        posfeats = [i[1:] for i in item]
                        outform, outfeats =  mult_generator(root, posfeats)
                    else:
                        # We need to generate it
                        token, pos, feats = item
                        if not pos:
                            # generator needs a POS; without one just
                            # append the token
                            output1.append(token); morph.append(None)
                            continue
                        outform, outfeats = generator(token, feats, pos=pos)
                    # Include only first max_gen_forms forms
                    if limit_forms:
                        outform = outform[:Seg.max_gen_forms]
                        outfeats = outfeats[:Seg.max_gen_forms]
                    # If there are multiple gen outputs, separate by |
                    form = '|'.join(outform)
                    output1.append(form); morph.append(outfeats)
                    generated = True
                else:
                    output1.append(item); morph.append(None)
            cleaned_trans.append(output1); morphology.append(morph)
        if verbosity:
            print("  Cleaned: {}".format(cleaned_trans))
        # Sort so that failed generations come last
        ungen_strings = []; ungen_morph = []
        gen_strings = []; gen_morph = []
        for strings, feats in zip(cleaned_trans, morphology):
            if any([Token.is_ungen(s) for s in strings]):
                ungen_strings.append(strings); ungen_morph.append(feats)
            else:
                gen_strings.append(strings); gen_morph.append(feats)
        cleaned_trans = gen_strings + ungen_strings
        morphology = gen_morph + ungen_morph
#        cleaned_trans.sort(key=lambda o: any([Token.is_ungen(oo) for oo in o]))
        # Join strings indicated by join character: Madrid `pe => Madrid-pe
        Seg.join_toks_in_strings(cleaned_trans, morphology)
        self.cleaned_trans = cleaned_trans
#        print("cleaned trans: {}".format(cleaned_trans))
        self.morphology = morphology
        self.generated = True

    def has_child(self):
        return len(self.segments) > 1

    ## Generating final translations

    def finalize(self, index, first=False, choose=False, verbosity=0):
        """
        Create final translation strings for this Seg. If html is True,
        set the HTML markup for the Seg as a colored segment in source
        and dropdown menu in target, given its position in the sentence.
        """
        # No translation
        if not self.cleaned_trans:
            self.final = [Seg.clean_spec(' '.join(self.tokens), False)]
            self.final_morph = []
            return
        # T Group strings associated with each choice
        choice_tgroups = []
        capitalized = False
        choice_list = self.record.choices if self.record else None
        # Final source segment output
        tokens = self.token_str
        orig_tokens = self.original_token_str
        # Currently selected translation
        trans1 = ''
        if self.is_punc:
            trans = self.translation[0][0]
            self.final = [trans]
            self.final_morph = [None]
            return
        multtrans = True
        final = []
        final_morph = []
        for tindex, (t, tgroups, tmorph) in enumerate(zip(self.cleaned_trans, self.tgroups, self.morphology)):
            # get all legitimate combinations of output strings and morphological features for constituent Segs
#            print("current final {}".format(self.final))
#            print("current morph {}".format(self.final_morph))
            tgforms, tgmorph, tggroups, multtrans = self.get_tchoices(t, tgroups, tmorph, multtrans, tindex)
#            print("tgforms {}".format(tgforms))
            # tgforms and tgmorph are pairs including scores
            final.extend(tgforms)
            final_morph.extend(tgmorph)
            choice_tgroups.extend(tggroups)
        if final:
            final.sort(key=lambda f: f[1])
            final_morph.sort(key=lambda m: m[1])
            self.final = [f[0] for f in final][:Seg.max_final]
            self.final_morph = [m[0] for m in final_morph][:Seg.max_final]
#            print("final {}".format(self.final))
            if self.record:
                self.record.choice_tgroups = choice_tgroups

#    def capitalize_first(self, tokens):
#        """Capitalize tokens if in first place."""
#        capitalized = False
#        if ' ' in tokens:
#            toks = []
#            tok_list = tokens.split()
#            for tok in tok_list:
#                if capitalized:
#                    toks.append(tok)
#                elif self.source.is_punc(tok):
#                    toks.append(tok)
#                else:
#                    toks.append(tok.capitalize())
#                    capitalized = True
#            tokens = ' '.join(toks)
#        else:
#            tokens = tokens.capitalize()

    @staticmethod
    def postproc_tstring(string):
        """Make final replacements to translation string."""
        return string.replace("'", "’").replace('_', ' ')

#    @staticmethod
#    def postproc_punc(string):
#        """Make final replacements to punctuation (a string with possibly multiple
#        punctuation characters."""
#        if '"' in string:
#            return string.replace('"', '\"')
#        return string

    def agree_disambig(self, combination, morph, disamb_agree):
        """Check that disamb_agree constraints are matched in combining
        combination with new string that has features in morph."""
        prev_value = -1
        next_value = -1
        for features, value in disamb_agree:
            for feature in features:
                for t, g, m in combination:
                    if not m:
                        continue
                    if feature in m:
                        # only one feature needs to match
                        prev_value = m.get(feature)
                        break
                if prev_value != -1:
                    break
            if prev_value != -1:
                for feature in features:
                    if feature in morph:
                        next_value = morph.get(feature)
                        # only one feature needs to match
                        if next_value is not prev_value:
                            return False
                        return True
        return True

    def combine_trans(self, trans_morph, init_score):
        """
        Return all legitimate combinations of trans strings and
        associated features, skipping over those that violate
        within-sentence morphological constraints.
        """
#        print("Combining {} with init {}".format(trans_morph, init_score))
        combinations = [([tm], i+init_score) for i, tm in enumerate(trans_morph[0])]
        disamb_agree = self.target.disambig_agree
        for items in trans_morph[1:]:
            new_combinations = []
            for j, (trans, group, morph) in enumerate(items):
#                print(" trans {} morph {}, j {}".format(trans, morph, j))
                for combination, k in combinations:
#                    print("  combination {}, k {}".format(combination, k))
                    agree = True
                    if disamb_agree and morph:
                        agree = self.agree_disambig(combination, morph, disamb_agree)
                    if agree:
                        new_combination = combination + [(trans, group, morph)], j + k
#                        print(" new comb {}".format(new_combination))
                        new_combinations.append(new_combination)
#                    else:
#                        print("  REJECTED combination {} with {}/{}".format(combination, trans, morph))
            combinations = new_combinations
        return combinations

    def get_tchoices(self, translation, tgroups, tmorph, multtrans, tindex):
        """Create all combinations of word sequences."""
        tg_expanded = []
        multtrans = True
        if self.special:
            trans = translation[0]
            tgcombs = [[[(trans, '', '')], 0]]
            # There can't be multiple translations for special sequences, can there?
            multtrans = False
        else:
            for tt, tg, tm in zip(translation, tgroups, tmorph):
#                print("tt {}, tg {}, tm {}".format(tt, tg, tm))
                tg = Group.make_gpair_name(tg)
                if '(' in tt:
                    # Get rid of parentheses around optional elements
                    tt = ['', tt[1:-1]]
                else:
                    # Separate multiple generation options
                    tt = tt.split('|')
                # Add tg group string and associated morphology to each choice
                if tm:
                    tg_expanded.append([(ttt, tg, tmm) for ttt, tmm in zip(tt, tm)])
                else:
                    tg_expanded.append([(ttt, tg, None) for ttt in tt])
            tgcombs = self.combine_trans(tg_expanded, tindex)
#            tgcombs = allcombs(tg_expanded)
#        print("tgcombs {}".format(tgcombs))
#        tgcombs = [tgc[0] for tgc in tgcombs]
#        tgcombs.sort()
        tgforms = []
        tgmorphology = []
        tggroups = []
        for ttg, score in tgcombs:
#            print("ttg {}, score {}".format(ttg, score))
            # "if tttg[0]" prevents '' from being treated as a token
            tgform = ' '.join([tttg[0] for tttg in ttg if tttg[0]])
            tgform = Seg.postproc_tstring(tgform)
            tgmorph = [tttg[2] for tttg in ttg if tttg[2]]
#            print("form {}, morph {}, score {}".format(tgform, tgmorph, score))
            tgforms.append((tgform, score))
            tgmorphology.append((tgmorph, score))
            tggroups.append("||".join([tttg[1] for tttg in ttg if tttg[0]]))
        ntgroups = len(tgroups)
        ntggroups = len(tggroups)
        if (ntgroups == 1) and (ntggroups == 1):
            multtrans = False
        return tgforms, tgmorphology, tggroups, multtrans

    ## Web app

    def set_source_html(self, first=False):
        """Set the HTML for the source side of this Seg."""
        cap = first and self.sentence.capitalized
        tokstr = self.original_token_str
        tokstr = clean_sentence(tokstr, capitalize=cap)
        self.source_html = "<span class='fuente' style='color:{};'> {} </span>".format(self.color, tokstr)

    def get_gui_source(self, paren_color='Silver'):
        return "<span class='fuente' style='color:{};'> {} </span>".format(self.color, self.token_str)

#    def get_trans_strings(self, index, first=False, choose=False, verbosity=0):
#        """Get the final translation strings for this Seg."""

    def make_html(self, index, first=False, verbosity=0):
        # T Group strings associated with each choice
        choice_tgroups = []
        minimal = self.is_punc or (not self.translation and not self.special)
        self.color = Seg.tt_notrans_color if minimal else Seg.tt_colors[Seg.color_index % 5]
        if not minimal:
            Seg.color_index += 1
        self.set_source_html(first)
        transhtml = "<div class='dropdownable' ondrop='drop(event);' ondragover='allowDrop(event);'>"
        dropdown = "dropdown{}".format(index)
        boton = "boton{}".format(index)
        wrap = "wrap{}".format(index)
        trans_choice_index = 0
        capitalized = False
        choice_list = self.record.choices if self.record else None
        # Final source segment output
        tokens = self.token_str
        orig_tokens = self.original_token_str
        # Currently selected translation
        trans1 = ''
        if minimal:
            trans = self.final[0]
            trans1 = trans
            if '"' in trans:
                trans = trans.replace('"', '\"')
            transhtml += "<div class='dropdown' id='{}' style='cursor:default'>".format(boton)
            transhtml += trans + "</div></div>"
            self.html = (tokens, self.color, transhtml, index, trans1, self.source_html)
            return
        # No dropdown if there's only 1 translation
        ntgroups = len(self.tgroups)
        multtrans = True
        ntggroups = len(self.final)
        if (ntgroups == 1) and (ntggroups == 1):
            multtrans = False
        for tcindex, tchoice in enumerate(self.final):
            # ID for the current choice item
            choiceid = 'opcion{}.{}'.format(index, trans_choice_index)
            # The button itself
            if tcindex == 0:
                trans1 = tchoice
                if not multtrans:
                    # Only translation; no dropdown menu
                    transhtml += "<div class='dropdown' id='{}' ".format(boton)
                    transhtml += "style='background-color:{};cursor:grab' draggable='true' ondragstart='drag(event);'>{}</div>".format(self.color, tchoice)
                else:
                    # First translation of multiple translations; make dropdown menu
                    transhtml += '<div draggable="true" id="{}" ondragstart="drag(event);">'.format(wrap)
                    transhtml += '<div onclick="dropdownify(' + "'{}')\"".format(dropdown)
                    transhtml += " id='{}' class='dropdown' style='background-color:{};cursor:context-menu'>{} ▾</div>".format(boton, self.color, tchoice)
            else:
                # Choice in menu under button
                if trans_choice_index == 1:
                    # Start menu list
                    transhtml += "<div id='{}' class='content-dropdownable'>".format(dropdown)
                transhtml += "<div class='segopcion' id='{}' onclick='changeTarget(".format(choiceid)
                transhtml += "\"{}\", \"{}\")'".format(boton, choiceid)
                transhtml += ">{}</div>".format(tchoice)
            trans_choice_index += 1
        if not self.translation and not self.special:
            trans1 = orig_tokens
            # No translations suggested: button for translating as source
            multtrans = False
            transhtml += "<div class='dropdown' id='{}'  style='cursor:grab' draggable='true' ondragstart='drag(event);'>".format(boton)
            transhtml += orig_tokens
            transhtml += "</div>"
        if multtrans:
            transhtml += '</div></div>'
        transhtml += '</div>'
        self.html = (orig_tokens, self.color, transhtml, index, trans1, self.source_html)

    def unseg_tokens(self):
        """Rejoin tokens in original_token_str that were segmented when
        the Sentence was created."""
        toksegs = self.sentence.toksegs
        if toksegs:
            remove = []
            for triple in toksegs:
                tok, seg, index = triple
                if index in self.indices:
                    # The tokseg is in this Seg; join it
                    self.original_token_str = self.original_token_str.replace(' '.join(seg), tok)
                    remove.append(triple)
            for triple in remove:
                toksegs.remove(triple)

    @staticmethod
    def remove_spec_pre(string):
        """Remove special prefixes, for example, '%ND~'."""
        if '%' in string:
            string = ''.join(Seg.special_re.split(string))
        return string

    @staticmethod
    def clean_spec(string, specpre=True):
        """Remove special prefixes and connecting characters."""
        if specpre:
            string = Seg.remove_spec_pre(string)
        # prefix ~
        if string[0] == '~':
            string = string[1:]
        # connecting _ and ~
        for c in ['  ', '_', '~', '+']:
            string = string.replace(c, ' ')
        return string

    @staticmethod
    def join_toks(string):
        """Join tokens as specified by the join character."""
        return string.replace(' ' + Seg.join_tok_char, '')

    @staticmethod
    def join_toks_char(strings, features):
        """Join two tokens, the second of which starts with join_tok_char."""
        if Seg.join_tok_char in strings[-1]:
            strings[-2:] = [strings[-2] + strings[-1][1:]]
            features[-2:] = [None]
            return strings, features
#            return [strings[0] + strings[1][1:]]

    @staticmethod
    def join_toks_in_strings(stringlists, featlists):
        """Join tokens in each item in list of strings."""
        for i, (stringlist, featlist) in enumerate(zip(stringlists, featlists)):
            # If there are two and the 2nd starts with join_tok_char, join them
            joined = Seg.join_toks_char(stringlist, featlist)
            if joined:
                stringlists[i] = joined[0]
                featlists[i] = joined[1]
            else:
                for j, string in enumerate(stringlist):
                    if Seg.join_tok_char in string:
                        stringlists[i][j] = Seg.join_toks(string)

class SuperSeg(Seg):
    """SuperSegment: joins Seg instances into larger units, either via a
    Join rule or a Group."""

    def __init__(self, segmentation, segments=None, features=None, name=None, join=None, verbosity=0):
        Seg.__init__(self, segmentation)
        self.segments = segments
        self.name = name
        self.join = join
        # If join is a group, this is a list of features (or True if there are none), one for search segment
        self.features = features
        self.order = list(range(len(segments)))
        self.head_seg = segments[join.head_index]
        self.head_tok = self.head_seg.head_tok
        # This has to happen before head attributes are set
        self.apply_changes(verbosity=verbosity)
        self.shead = self.head_seg.shead
        self.scats = self.head_seg.scats
        self.thead = self.head_seg.thead
        if self.head_seg.special:
#            any([s.special for s in self.segments]):
            self.special = True
        ## Copy properties of sub-Segments
        self.record = self.segments[0].record
        raw_tokens = []
        token_str = []
        # Indices are those of sub-Segments.
        self.indices = reduce_lists([seg.indices for seg in segments])
        self.indices.sort()
        self.translation = []
        gname = []
        self.cleaned_trans = []
        self.tgroups = []
        self.original_token_str = ' '.join([seg.original_token_str for seg in self.segments])
        # Rejoin source tokens segmented during Sentence creation
        self.unseg_tokens()
        for i in self.order:
            if i < 0:
                # This represents a target token with no corresponding source token
                continue
            segment = self.segments[i]
            if verbosity:
                print("Setting SuperSeg properties, segment {}, current ct {}".format(segment, self.cleaned_trans))
                print(" Segment cleaned_trans: {}, translation {}".format(segment.cleaned_trans, segment.translation))
            if self.cleaned_trans:
                if segment.cleaned_trans:
                    self.cleaned_trans = [ct1 + ct2 for ct1 in self.cleaned_trans for ct2 in segment.cleaned_trans]
            else:
                self.cleaned_trans = segment.cleaned_trans
            if self.tgroups:
                if segment.tgroups:
                    # Segment may have no translation (e.g., "de")
                    self.tgroups = [tg1 + tg2 for tg1 in self.tgroups for tg2 in segment.tgroups]
            else:
                self.tgroups = segment.tgroups
            self.translation.append(segment.translation)
            raw_tokens.append(segment.raw_token_str)
            token_str.append(segment.token_str)
            gname.append(segment.gname or '')
        self.gname = "++".join(gname)
        self.raw_token_str = ' '.join(raw_tokens)
        self.token_str = ' '.join(token_str)
        # calculate depth from depth of segment components
        self.depth = self.get_depth()

    def __repr__(self):
        if self.name:
            return self.name
        elif self.segments:
            return ">>" + "++".join([seg.token_str for seg in self.segments]) + "<<"
        else:
            return "SuperSeg"

    def get_depth(self):
        d = 1
        d += max([segment.depth for segment in self.segments])
        return d

    def count_segments(self):
        """Return the number of leaf Segments."""
        return sum([segment.count_segments() for segment in self.segments])

    def apply_changes(self, verbosity=1):
        """Implement the changes to features and order specified in the Join or Group instance."""
#        print("Superseg {} applying changes".format(self))
        self.join.apply(self, verbosity=verbosity)

class Segment(Seg):
    """Sentence segmentation segment, realization of a Group, possibly
    merged with another. Displayed in GUI."""

    def __init__(self, segmentation, indices, translation, tokens, color=None, space_before=1,
                 treetrans=None, sfeats=None, tgroups=None,
                 head=None, tok=None, spec_indices=None, session=None, gname=None, is_punc=False):
        Seg.__init__(self, segmentation)
#        print("Creating Segment with translation: {}".format(translation))
        if sfeats:
            sfeat_dict = sfeats[0]
            self.shead_index = 0
            self.shead = [(sfeat_dict.get('root'), sfeat_dict.get('features'), sfeat_dict.get('pos'))]
            self.scats = sfeat_dict.get('cats', set())
        else:
            self.shead_index = -1
            self.shead = None
            self.scats = None
        self.treetrans = treetrans
        self.indices = indices
        self.space_before = space_before
        # Token instance for the head if there is one
        self.head_tok = tok
        # Are there any alternatives among the translations?
        self.any_choices = any(['|' in t for t in translation])
        # For each translation alternative, separate words, each of which can have alternatives (separated by '|').
        # self.translation is a list of lists
        self.translation = [(t.split() if isinstance(t, str) else t) for t in translation]
        self.cleaned_trans = None
        self.tokens = tokens
        self.token_str = ' '.join(tokens)
        self.raw_token_str = self.token_str[:]
        self.original_tokens = tokens
        self.original_token_str = ' '.join(self.original_tokens)
        # If there are special tokens in the source language, fix them here.
        if self.head_tok.special:
            self.special = True
            # Create the source and target strings without special characters
            if translation:
                self.cleaned_trans = self.translation[:] #translation[:]
            else:
                spec_toks = [t for t in tokens if t[0] != '~']
                self.cleaned_trans = [spec_toks]
                tgroups = [spec_toks]
            self.token_str = Seg.clean_spec(self.token_str)
            self.original_token_str = Seg.clean_spec(self.original_token_str)
        if '~' in self.original_token_str or '+' in self.original_token_str:
            self.original_token_str = Seg.clean_spec(self.original_token_str)
        if '~' in self.token_str or '+' in self.token_str:
            self.token_str = Seg.clean_spec(self.token_str)
        if not self.cleaned_trans:
            self.cleaned_trans = self.translation[:]
        # Join tokens in cleaned translation if necessary
        if treetrans:
            thead_indices = [g.head_index for g in treetrans.tgroups]
            self.thead = [o[i] for i, o in zip(thead_indices, self.cleaned_trans)]
        else:
            self.thead = None
        self.color = color
        # Whether this segment is just punctuation
        self.is_punc = is_punc
        # Name of the group instantiated in this segment
        self.gname = gname
        # Triples for each merger with the segment
        # Target-language groups
        self.tgroups = tgroups or [[""]] * (len(self.translation) or 1)
#        # Target-language group strings, ordered by choices; gets set in finalize()
#        self.choice_tgroups = None
        # The session associated with this segmentation segment
        self.session = session
        # Create a record for this segment if there's a session running and it's not punctuation
        if session and session.running and not self.source.is_punc(self.token_str):
            self.record = self.make_record(session, segmentation.sentence)
        else:
            self.record = None

    def __repr__(self):
        """Print name."""
        return ">>{}<<".format(self.token_str)

    def count_segments(self):
        """Return the number of leaf Segments."""
        return 1

    ## Record

    def make_record(self, session=None, sentence=None):
        """Create the SegRecord object for this Segment."""
        if sentence:
            return SegRecord(self, sentence=sentence.record, session=session)

    ## Matching

    def has_child(self):
        return len(self.tokens) > 1

class SNode:
    """Sentence token and its associated analyses and variables."""

    def __init__(self, index, analyses, sentence, raw_indices,
                 toks=None, tok=None, toktype=1): #, del_indices=None):
        # Raw form in sentence (possibly result of segmentation)
        self.token = tok.fullname
        # Token type (used to distinguish prefix from suffix punctuation.
        self.toktype = toktype
        # Original form of this node's token (may be capitalized)
        # Token objects
        self.toks = toks
        # Head Token object
        self.tok = tok
        # Position in sentence
        self.index = index
        # Positions in original sentence
        self.raw_indices = raw_indices
        # List of analyses
        if analyses and not isinstance(analyses, list):
            analyses = [analyses]
        if not analyses:
            analyses = [{'root': self.token}]
        self.analyses = analyses
        # Back pointer to sentence
        self.sentence = sentence
        # Raw sentence tokens associated with this SNode
        self.raw_tokens = [sentence.tokens[i] for i in self.raw_indices]
        # Any deleted tokens to the left or right of the SNode token
        self.left_delete = None
        self.right_delete = None
        token_headi = self.raw_tokens.index(self.token)
        if token_headi != 0:
            self.left_delete = self.raw_tokens[:token_headi]
        if token_headi != len(self.raw_tokens) - 1:
            self.right_delete = self.raw_tokens[token_headi:]
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
        if '~' in self.tok.name:
            # A special phrase (MWE) that bypasses POS tagging
            return False
        a = self.get_analysis()
        return not (a.get('pos') or a.get('cats') or a.get('features'))

    def is_special(self):
        """Is this 'special' (for example, a number)?"""
        return Token.is_special(self.token)

    def get_pos(self):
        """Get the POSs for the analyses."""
        return [a.get('pos', '') for a in self.analyses]

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
            self.variables['features'] = EMPTY
        else:
            # GNodes associated with this SNode: 0, 1, or 2
            upper = set(self.gnodes)
            self.svar('gnodes', "w{}->gn".format(self.index), set(),
                      upper,
                      1, 1, ess=True)
            # Features
            features = self.get_features()
            if len(features) > 1:
                self.lvar('features', 'w{}f'.format(self.index),
                          [], features, 1, 1)
            else:
                # Only one choice so features are determined for this SNode
                self.variables['features'] = \
                   DetLVar('w{}f'.format(self.index), features)

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
        """Does this node match a negative group condition, with grp_spec
        either a FeatStruc
        or a category? Look through analyses until one *fails* to match."""
        for grp_spec in grp_specs:
            matched = True
            # See if any analysis fails to match this grp_spec; if not succeed
            for analysis in self.analyses:
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
                        u_features = sn_feats.unify_FS(grp_spec, strict=True, verbose=verbosity>1)
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
            if matched:
                return True
        # None matched
        return False

    def match(self, grp_item, grp_feats, verbosity=0, debug=False):
        """Does this node match the group item (word, root, category) and
        any features associated with it?"""
        # 2020.9.8: added POS to match output (3rd element in tuple)
        # If this is a punctuation node, it can't match a group item unless the item is also punctuation (not alphanum)
        if self.is_punc() and grp_item.isalnum():
            return False
        if verbosity > 1 or debug:
            print('   SNode {} with features {} trying to match item {} with features {}'.format(self, self.analyses, grp_item, grp_feats.__repr__()))
        # If item is a category, don't bother looking at token
        is_cat = Token.is_cat(grp_item)
        is_spec = Token.is_special(grp_item)
        if is_spec and self.tok.special:
            if verbosity > 1 or debug:
                print("Special entry {} for {}".format(grp_item, self.token))
            token_type = self.token.split('~')[0]
            if token_type.startswith(grp_item):
                # Special group item matches node token (grp_item could be shorter than token_type)
                return None
        # Check whether the group item is really a set item (starting with '$$'); if so, drop the first '$' before matching
        if is_cat and Token.is_set(grp_item):
            grp_item = grp_item[1:]
        # If group token is not cat and there are no group features, check for perfect match
        if not is_cat and not grp_feats:
            if self.tok.name == grp_item:
                if verbosity or debug:
                    print("    Matches trivially")
                return None
        # Go through analyses, checking cat, root, and features (if any group features)
        results = []
        # 2018.2.23: updated to exclude case where SNode has no analyses; it always does
        #  also nodes can match group category even if they don't have associated groups of their own
        for analysis in self.analyses:
            node_features = analysis.get('features')
            node_cats = analysis.get('cats', [])
            node_root = analysis.get('root', '')
            node_pos = analysis.get('pos', '')
            node_roots = None
            if verbosity > 1 or debug:
                print("    Trying to match analysis: {}/{}/{} against group {}".format(node_root, node_cats, node_features.__repr__(), grp_item))
            # This next section was for within-POS ambiguity (Spa ser|ir)
            # Handle it differently in mit'mit'a?
#            if '_' in node_root: # and not Seg.special_re.match(node_root):
#                # Numbers and other special tokens also contain '_'
#                node_roots = []
##                if node_root.count('_') > 1:
#                print("node_root: {}".format(node_root))
#                # An ambiguous root in analysis, for example, ser|ir in Spa
#                r, p = node_root.split('_')
#                for rr in r.split('|'):
#                    node_roots.append(rr + '_' + p)
            # Match group token
            if is_cat:
                if grp_item in node_cats:
                    if verbosity > 1 or debug:
                        print("      Succeeding for cat {} for node with root {}".format(grp_item, node_root))
                else:
                    # Fail because the group category item doesn't match the node categories
                    if verbosity > 1 or debug:
                        print("      Failing because group cat item doesn't match node cats")
                    continue
            else:
                # Not a category, has to match the root
                if node_roots:
                    if verbosity > 1 or debug:
                        print("      Checking node roots {}".format(node_roots))
                    m = firsttrue(lambda x: x == grp_item, node_roots)
                    if m:
                        node_root = m
                    elif grp_item != node_root:
                        continue
                elif grp_item != node_root:
                    continue
            if verbosity > 1 or debug:
                print("      Matched token")
            # Match features if there are any
            if node_features:
                if grp_feats:
                    # 2015.7.5: strict option added to force True feature in grp_features
                    # to be present in node_features, e.g., for Spanish reflexive
                    if verbosity > 1 or debug:
                        print("    Unifying n feats {} with g feats {}".format(node_features, grp_feats.__repr__()))
                    nfeattype = type(node_features)
                    if nfeattype == FSSet:
                        u_features = node_features.unify_FS(grp_feats, strict=True, verbose=verbosity>1)
                    else:
                        u_features = simple_unify(node_features, grp_feats, strict=True)
                    if u_features != 'fail':
                        # SUCCEED: matched token and features
                        results.append((node_root, u_features, node_pos))
                else:
                    # SUCCEED: matched token and no group features to match
                    results.append((node_root, node_features, node_pos))
            else:
                # SUCCEED: group has features but node doesn't
                results.append((grp_item, grp_feats, node_pos))
        if results:
            if verbosity > 1 or debug:
                print("  Returning match results: {}".format(results))
            return results
        return False

class GInst:

    """Instantiation of a group; holds variables and GNode objects."""

    def __init__(self, group, sentence, head_index, snode_tuple, index):
        # The Group object that this "instantiates"
        self.group = group
        self.sentence = sentence
        self.source = sentence.language
        self.target = sentence.target
        # Index of group within the sentence
        self.index = index
        # Index of SNode associated with group head
        self.head_index = head_index
        # List of GNodes
        self.nodes = []
        # Index of the GNode that is the head
        ghead_index = group.head_index
        for index, sntups in enumerate(snode_tuple):
            # sntups is a list of snindex, match features, token, create? tuples
            deleted = False
            for snindex, match, token, create in sntups:
                if not create:
                    deleted = True
                    break
            if deleted:
                # If this is before where the head should be, decrement that index
                if index <= ghead_index:
                    ghead_index -= 1
                # Increment index so indices correspond to raw group tokens
                continue
            else:
                self.nodes.append(GNode(self, index, sntups))
        # The GNode that is the head of this GInst
        if ghead_index > len(self.nodes) - 1:
            print("Problem instantiating {} for {}; head index {}".format(group, self.nodes, ghead_index))
        self.ghead_index = ghead_index
        self.head = self.nodes[ghead_index]
        # Dict of variables specific to this group
        self.variables = {}
        # List of target language groups, gnodes, tnodes
        self.translations = []
        self.ngnodes = len(self.nodes)
        # TreeTrans instance for this GInst; saved here to prevent multiple TreeTrans translations
        self.treetrans = None
        # Indices of GInsts that this GINst depends on; set in Sentence.lexicalize()
        self.dependencies = None
        # Possible snode indices for lexical and category nodes.
        self.sindices = [[], []]

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
        if self.dependencies:
            self.variables['deps'] = DetVar('deps{}'.format(self.index), self.dependencies)
        else:
            self.variables['deps'] = EMPTY
        # GNode indices for this GInst (determined)
        self.variables['gnodes'] = DetVar('g{}->gnodes'.format(self.index), {gn.sent_index for gn in self.nodes})
        # Abstract GNode indices for GInst (determined)
        # SNode positions of GNodes for this GInst
        self.svar('gnodes_pos', 'g{}->gnodes_pos'.format(self.index),
                  set(), set(cand_snodes), self.ngnodes, self.ngnodes)
        # Determined variable for within-source agreement constraints, gen: 0}
        agr = self.get_agr()
        if agr:
            self.variables['agr'] = DetVar('g{}agr'.format(self.index), agr)

    def set_translations(self, verbosity=0):
        """Find the translations of the group in the target language."""
        translations = self.group.get_translations()
        # Sort group translations by their translation frequency
        Group.sort_trans(translations)
        if verbosity:
            print("Setting translations for {}: {}".format(self, translations))
        # If alignments are missing, add default alignment
        for i, t in enumerate(translations):
            if len(t) == 1:
                translations[i] = [t[0], {}]
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
            # Make any TNodes (for target words not corresponding to any source words)
            tnodes = []
            # Target group has more nodes than source group.
            # Indices of groups that are not empty:
            full_t_indices = set(alignment)
            empty_t_indices = set(range(nttokens)) - full_t_indices
            if empty_t_indices:
                for i in empty_t_indices:
                    empty_t_token = tgroup.tokens[i]
                    empty_t_feats = tgroup.features[i] if tgroup.features else None
                    tnodes.append(TNode(empty_t_token, empty_t_feats, tgroup, i, self))
            # Deal with individual gnodes in the group
            gnodes = []
            tokens = tgroup.tokens
            features = tgroup.features
            # Go through source group nodes, finding alignments and agreement constraints
            # with target group nodes
            for gnode in self.nodes:
                gn_index = gnode.index
                gn_token = gnode.token
                # Align gnodes with target tokens and features
                targ_index = alignment[gn_index]
                if targ_index < 0:
                    # This means there's no target language token for this GNode.
                    continue
                agrs = None
                if s2t_dict.get('agr'):
                    agr = s2t_dict['agr'][gn_index]
                    if agr:
                        tindex, stagr = agr
                        targ_index = tindex
                        agrs = stagr
                if gnode.special:
                    spec_trans = self.source.translate_special(gn_token)
                    token = spec_trans
                else:
                    token = tokens[targ_index]
                feats = features[targ_index] if features else None
                gnodes.append((gnode, token, feats, agrs, targ_index))
            self.translations.append((tgroup, gnodes, tnodes))

class GNode:

    """Representation of a single node (word, position) within a GInst object."""

    def __init__(self, ginst, index, snodes):
        self.ginst = ginst
        self.index = index
        self.sentence = ginst.sentence
        self.snode_indices = [s[0] for s in snodes]
        self.snode_anal = [s[1] for s in snodes]
        self.snode_tokens = [s[2] for s in snodes]
        # Whether this is the head of the group
        self.head = index == ginst.group.head_index
        # Group word, etc. associated with this node
        gtoken = ginst.group.tokens[index]
        self.gtoken = gtoken
        # If this is a set node, use the sentence token instead of the cat name
        if Token.is_set(gtoken):
            self.token = self.sentence.nodes[snodes[0][0]].token
        else:
            self.token = gtoken
        if len(self.snode_tokens) == 1 and Token.is_special(self.snode_tokens[0]):
            self.token = self.snode_tokens[0]
        # Whether the associated token is abstract (a category)
        self.cat = Token.is_cat(self.token)
        # Whether the associated token is special (for example, a numeral).
        self.special = Token.is_special(self.token)
        # Features associated with this group node
        groupfeats = ginst.group.features
        if groupfeats:
            self.features = groupfeats[index]
        else:
            self.features = None
        self.variables = {}

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

    def __init__(self, token, features, group, index, ginst):
        self.token = token
        self.features = features
        self.group = group
        self.index = index
        self.ginst = ginst

    def __repr__(self):
        return "~{}|{}".format(self.ginst, self.token)

class TreeTrans:
    """Translation of a tree: a group or two or more groups joined by merged nodes."""

    def __init__(self, segmentation, tree=None, ginst=None,
                 gnode_dict=None, group_attribs=None,
                 # Whether the tree has any abstract nodes (to merge with concrete nodes)
                 any_anode=False, index=0, top=False, verbosity=0):
        # The segmentation generating this translation
        self.segmentation = segmentation
        self.source = segmentation.source
        self.target = segmentation.target
        self.sentence = segmentation.sentence
        # Dict keeping information about each gnode; this dict is shared across different TreeTrans instances
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
        # Tgroups in output order for each translation
        self.ordered_tgroups = []
        # Merged group indices
        self.mergers = []
        snode_indices = list(tree)
        snode_indices.sort()
        self.snode_indices = snode_indices
        self.snodes = [self.sentence.nodes[i] for i in snode_indices]
        self.sol_gnodes_feats = \
           [segmentation.gnodes_feats[i] for i in snode_indices]
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
        # Create the solver for ordering elements within the TreeTrans
        self.solver = Solver(self.constraints, self.dstore, description='target tree realization',
                             verbosity=verbosity)
        # These are produced in self.build(); each only applies to the latest translation
        self.node_features = None
        self.group_nodes = None
        self.agreements = None
        self.nodes = []
        # Accumulate the nodes found in build()
        self.all_nodes = []
        # Final outputs; different ones have alternate word orders
        self.outputs = []
        # Strings representing outputs
        self.output_strings = []
        # Cache for node mergers
        self.cache = {}
        if verbosity:
            print("Created TreeTrans {}".format(self))
            print("  Gnode dict: {}".format(self.gnode_dict))
            print("  Indices: {}, tgroups {}, tnodes {}".format(self.tree, self.tgroups, self.tnodes))
            print("  Sol gnodes feats: {}".format(self.sol_gnodes_feats))

    def __repr__(self):
        return "{{{}}}->".format(self.ginst)

    def display(self, index):
        print("{}  {}".format(self, self.output_strings[index]))

    def display_all(self):
        for index in range(len(self.outputs)):
            self.display(index)

    @staticmethod
    def output_string(output):
        """Create an output string from a list."""
        out = []
        # False if there is a (root, pos, feats) tuple because generation
        # is delayed
        generated = True
        for word_list in output:
            if len(word_list) == 1:
                wl0 = word_list[0]
                out.append(wl0)
                if isinstance(wl0, list):
                    generated = False
            elif isinstance(word_list[0], list):
                generated = False
                out.append(word_list)
            else:
                out.append('|'.join(word_list))
        if generated:
            out = ' '.join(out)
        return out

    def make_cache_key(self, gn_tuple, verbosity=0):
        """Make the key for the cache of gnode info."""
        if not gn_tuple:
            return
        cache_key = None
        cache_key = gn_tuple[0], gn_tuple[-1]
        return cache_key

    def get_cached(self, gn_tuple, cache_key=None, verbosity=0):
        """Get gnode information if already cached."""
        if not gn_tuple:
            return
        if not cache_key:
            cache_key = self.make_cache_key(gn_tuple, verbosity=verbosity)
        if cache_key in self.cache:
            # merged nodes found in local cache
            cached = self.cache[cache_key]
            if verbosity > 1:
                print("   result already in cache: {}".format(cached))
            return cached
        return None

    def record_ind_feats(self, token='', tnode_index=-1, t_indices=None,
                         tposfeats=None,
#                         targ_feats=None, tpos='',
                         snode=None, node_index_map=None, verbosity=0):
        """
        Record index and target features in TreeTrans instance.
        """
#        print("RECORDING INDEX AND TARGET FEATURES")
#        print(" token {}, tnodeindex {}, tindices {}".format(token, tnode_index, t_indices))
#        print(" tposfeats {}".format(tposfeats))
#        print(" nodeindexmap {}".format(node_index_map))
        node_index_map[snode.index] = tnode_index
        if not t_indices:
            t_indices = []
        if not token:
            token = snode.token
#        for tpos, targ_feats in tposfeats:
        self.node_features.append([token, tposfeats, t_indices])
        if t_indices:
            targ_feats = tposfeats[0][0]
            feat_index = len(self.node_features) if token else []
            for t_index in t_indices:
                # NOTE: THIS IS WRONG BECAUSE IT ONLY USES ONE SET OF
                # TARGET FEATURES
                self.group_nodes[t_index] = [token, targ_feats, feat_index]
#            print(" group nodes {}".format(self.group_nodes))

    def cache_gnodes(self, cache_key=None, token="", tnode_index=-1,
                     t_indices=None, tg_merger_groups=None, targ_feats=None):
        self.cache[cache_key] = \
           (token, tnode_index, t_indices, tg_merger_groups, targ_feats)

    def merge_agr_feats(self, agrs, targ_feats, features, verbosity=0):
        """
        Cause features in features to agree with targ_features for pairs agrs,
        returning targ_features.
        """
#        print("{} merging agr features src {} trg {}".format(self, features,
#                                                             targ_feats.__repr__()))
        if not targ_feats:
            targ_feats = FeatStruct({})
        if agrs:
            # Use an (unfrozen) copy of target features
            targ_feats = targ_feats.copy(True)
            if verbosity:
                print("  Causing sfeats {} to agree with tfeats {}".format(features, targ_feats.__repr__()))
            if features:
                targ_feats = features.agree_FSS(targ_feats, agrs)
            if verbosity:
                print("   Now: {} to agree with tfeats {}".format(features, targ_feats.__repr__()))
        return targ_feats

    def adapt_feats(self, spos, sfeats, tfeats, verbosity=0):
        """
        Adapt source features to target based on POS and features conversions in
        POS.posconv and POS.featconv.
        """
        if verbosity:
            print("Adapt sfeats {} (spos: {}) to tfeats {}".format(sfeats.__repr__(),
            spos, tfeats.__repr__()))
        tposfeatlist = \
            self.source.adapt(spos, self.target.abbrev, sfeats, tfeats)
        if verbosity:
            print("Adapted {}".format(tposfeatlist))
        return tposfeatlist

    def build(self, tg_groups=None, tg_tnodes=None, cache=False,
              verbosity=0):
        """Unify translation features for merged nodes, map agr features from
        source to target,
        generate surface target forms from resulting roots and features.
        tg_groups is a combination of target groups.
        2019.5.27: Changed to reflect the disappearance of merge nodes.
        2020.9: Added POS and feature adaptation. Turning off caching for now.
        """
        if verbosity:
            print('BUILDING {} with tgroups {} and tnodes {}'.format(self, tg_groups, tg_tnodes))
            print("  SNodes: {}".format(self.snodes))
            print("  Sol gnodes feats: {}".format(self.sol_gnodes_feats))
        tnode_index = 0
        # Dictionary mapping source node indices to initial target node indices
        node_index_map = {}
        self.agreements, self.group_nodes = {}, {}
        self.node_features = []
        # reinitialize mergers
        self.mergers = []
        # Find the top-level tgroup
        top_group_attribs = list(itertools.filterfalse(lambda x: x[0] not in tg_groups, self.group_attribs))[0]
        if verbosity:
            print('Top group attribs: {}'.format(top_group_attribs))
        for snode, (gnodes, features, pos) in zip(self.snodes, self.sol_gnodes_feats):
            if verbosity:
                fstring = "   snode {}, gnodes {}, features {}, pos {}"
                print(fstring.format(snode, gnodes, features.__repr__(), pos))
            cache_key, token, targ_feats, agrs = None, None, None, None
            t_indices = []
            gnode = gnodes[0]
            if not gnode:
                # snode is not covered by any group
                self.record_ind_feats(tnode_index=tnode_index, snode=snode, node_index_map=node_index_map)
                tnode_index += 1
                continue
            if gnode not in self.gnode_dict:
                if verbosity > 1:
                    print("   not in gnode dict, skipping")
                continue
            gnode_tuple_list = self.gnode_dict[gnode]
            gnode_tuple = firsttrue(lambda x: x[0] in tg_groups, gnode_tuple_list)
            if verbosity > 1:
                print("   gnode_tuple: {}, list {}".format(gnode_tuple, gnode_tuple_list))
            if not gnode_tuple and verbosity:
                print("Something wrong with snode {}, gnodes {}, gnode_tuple_list {}, tg_groups {}".format(snode, gnodes, gnode_tuple_list, tg_groups))
            cache_key = self.make_cache_key(gnode_tuple)
            cached = self.get_cached(gnode_tuple, cache_key=cache_key, verbosity=verbosity)
            if cache and cached:
                # DISABLED FOR NOW (record_ind_feats doesn't work like this)
                # translation already in local cache
                tok, tn_i, t_i, x, t_feats = cached
                self.record_ind_feats(token=tok, tnode_index=tn_i,
                                      t_indices=t_i,
                                      targ_feats=t_feats, snode=snode,
                                      node_index_map=node_index_map)
            else:
                # translation not in local cache
                tgroup, token, targ_feats, agrs, t_index = gnode_tuple
                if len(tgroup.tokens) > 1:
                    t_indices.append((tgroup, t_index))
                else:
                    t_indices = [(tgroup, 0)]
                # Make target and source features agree as required
                targ_feats = self.merge_agr_feats(agrs, targ_feats, features,
                                                  verbosity=verbosity)
                # Adapt source to target features
                tposfeats = self.adapt_feats(pos, features, targ_feats,
                                             verbosity=0)
                self.record_ind_feats(token=token, tnode_index=tnode_index,
                                      t_indices=t_indices,
                                      tposfeats=tposfeats,
#                                      tpos=tpos, targ_feats=targ_feats,
                                      snode=snode,
                                      node_index_map=node_index_map)
                self.cache_gnodes(cache_key=cache_key, token=token,
                                  tnode_index=tnode_index,
                                  t_indices=t_indices, targ_feats=targ_feats)

            tnode_index += 1

        # Make indices for tgroup trees
        for src_index in self.tree:
            if src_index in node_index_map:
                self.ttree.add(node_index_map[src_index])
        # Add TNode elements
        tgnode_elements = []
        tginst, tnodes, agr, tgnodes = top_group_attribs
        if agr:
            self.agreements[tginst] = agr
            if verbosity > 1:
                print(" build(): tginst {} agr {}, agreements {}".format(tginst, agr, self.agreements))
        subtnodes = tg_tnodes[1] if len(tg_tnodes) > 1 else []
        # Incorporate TNodes into nodes and features of this TTrans
        self.add_tnodes(tnodes, subtnodes, tginst)
        return True

    def add_tnodes(self, tnodes, subtnodes, tginst):
        """Incorporate TNodes into nodes and features of TTrans."""
        for tnode in tnodes:
            features = tnode.features or FeatStruct({})
            src_index = len(self.node_features)
            self.ttree.add(src_index)
            index = [(tginst, tnode.index)]
            feat_index = len(self.node_features)
            self.node_features.append([tnode.token, ('', features), index])
            self.group_nodes[index[0]] = [tnode.token, features, feat_index]
        # TNodes in subTTs
        for tnode in subtnodes:
            features = tnode.features or FeatStruct({})
            src_index = len(self.node_features)
            self.ttree.add(src_index)
            index = [(tnode.group, tnode.index)]
            feat_index = len(self.node_features)
            self.node_features.append([tnode.token, ('', features), index])

    @staticmethod
    def get_root_POS(token):
        """Token may be something like guata_, guata_v, Ty_q_v."""
        if Token.is_special(token) or '_' not in token:
            return token, None
        root, x, pos = token.rpartition("_")
        if pos not in ['v', 'a', 'n']: # other POS categories possible?
            # the '_' is part of the word itself
            return token, None
        return root, pos

    def do_agreements(self, limit_forms=True, verbosity=0):
        """Do intra-group agreement constraints."""
        # Reinitialize nodes
        self.nodes = []
        if verbosity:
            print("{} doing agreements".format(self))
        for group, agr_constraints in self.agreements.items():
            for agr_constraint in agr_constraints:
                i1, i2 = agr_constraint[0], agr_constraint[1]
                feature_pairs = agr_constraint[2:]
                # Find the sentence nodes for the agreeing group nodes in the group_nodes dict
                agr_node1 = self.group_nodes[(group, i1)]
                agr_node2 = self.group_nodes[(group, i2)]
                agr_feats1, agr_feats2 = agr_node1[1], agr_node2[1]
                feat_index1, feat_index2 = agr_node1[2], agr_node2[2]
                # FSSets agr_feats1 and agr_feats2 have to be unfrozen before then can be made to agree
                if isinstance(agr_feats1, FeatStruct):
                    agr_feats1 = FSSet(agr_feats1)
                if isinstance(agr_feats2, FeatStruct):
                    agr_feats2 = FSSet(agr_feats2)
                agr_feats1 = agr_feats1.unfreeze(cast=False)
                agr_feats2 = agr_feats2.unfreeze(cast=False)
                af1, af2 = FSSet.mutual_agree(agr_feats1, agr_feats2, feature_pairs)
                # Replace the frozen FSSets with the modified unfrozen ones
                agr_node1[1], agr_node2[1] = af1, af2
                self.node_features[feat_index1][1] = af1
                self.node_features[feat_index2][1] = af2
        for token, features, index in self.node_features:
            pos, feats = features[0]
            root, rpos = TreeTrans.get_root_POS(token)
            if not pos:
                # There could be a POS specified
                pos = rpos
#            if verbosity:
            output = [token]
            if not pos:
                if self.target.postsyll:
                    token = self.target.syll_postproc(token)
                    output = [token]
            else:
                output = [[root, pf[0], pf[1]] for pf in features]
#                output = [[root, pos, features]]
            self.nodes.append([output, index])
            if verbosity:
                print("TT NODE {}: {}".format(index, output))

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
#            print("NODE I {}, F {}, C {}".format(index, forms, constraints))
            for tgroup, tg_index in constraints:
                if tgroup not in tgroup_dict:
                    tgroup_dict[tgroup] = []
                tgroup_dict[tgroup].append((index, tg_index))
#                print("TGROUP {}, TGROUP DICT {}".format(tgroup, tgroup_dict))
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
        self.variables['order_pairs'] = DetVar("order_pairs", set([tuple(positions) for positions in self.order_pairs]))
        self.variables['order'] = [IVar("o{}".format(i), set(range(nnodes)), rootDS=self.dstore, essential=True) for i in range(nnodes)]

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

    def realize(self, verbosity=0, display=False, all_trans=False, interactive=False):
        """Run constraint satisfaction on the order and disjunction constraints,
        and convert variable values to sentence positions."""
        generator = self.solver.generator(test_verbosity=verbosity, expand_verbosity=verbosity)
        try:
            proceed = True
            while proceed:
                # Run solver to find positions (values of 'order' variables)
                succeeding_state = next(generator)
                order_vars = self.variables['order']
                positions = [list(v.get_value(dstore=succeeding_state.dstore))[0] for v in order_vars]
                # list of (form, position) pairs; sort by position
                node_group_pos = list(zip(self.nodes, positions))
                node_group_pos.sort(key=lambda x: x[1])
                node_pos = [n[0] for n in node_group_pos]
                self.all_nodes.append(node_pos)
                # Groups and gnode indices in output order
                group_pos = [n[1] for n in node_pos]
                self.ordered_tgroups.append(group_pos)
                # just the form
                output = [n[0] for n in node_pos]
                self.outputs.append(output)
                output_string = output
                output_string = TreeTrans.output_string(output)
                self.output_strings.append(output_string)
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
