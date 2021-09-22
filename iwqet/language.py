#
#   Mainumby/Mit'mit'a: languages: dictionaries of lexical/grammatical entries
#
########################################################################
#
#   This file is part of the Mainumby project within the PLoGS metaproject
#   for parsing, generation, translation, and computer-assisted
#   human translation.
#
#   Copyleft 2014, 2015, 2016, 2017, 2020; HLTDI, PLoGS <gasser@indiana.edu>
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

# 2014.02.09
# -- Created
# (See mainumby for other history)
# 2020.09
# -- Mit'mit'a/Gyez: added support for feature conversion

from .entry import *
from .utils import firsttrue
from iwqet.morphology.utils import reduce_lists, firstindex
from iwqet.morphology.morpho import Morphology, POS
from iwqet.morphology.fs import FeatStruct
from iwqet.morphology.semiring import FSSet, TOP
from .geez import *

import os, yaml, re, copy

LANGUAGE_DIR = os.path.join(os.path.dirname(__file__), 'languages')

## Regexes for parsing language data
# Backup language abbreviation
# l...:
BACKUP_RE = re.compile(r'\s*l.*?:\s*(.*)')
## preprocessing function
#PREPROC_RE = re.compile(r'\s*pre*?:\s*(.*)')
# Segments (characters)
# seg...:
SEG_RE = re.compile(r'\s*seg.*?:\s*(.*)')
# Accent dictionary

ACC_RE = re.compile(r'\s*accent:\s*(.*)')
# Deaccent dictionary
# deaccent:
DEACC_RE = re.compile(r'\s*deaccent:\s*(.*)')
# Punctuation
# pun...:
PUNC_RE = re.compile(r'\s*pun.*?:\s*(.*)')
# Part of speech categories
# pos: v verbo
POS_RE = re.compile(r'\s*pos:\s*(.*)\s+(.*)')
# Feature abbreviations
# ab...:
ABBREV_RE = re.compile(r'\s*ab.*?:\s*(.*)')
# Term translations
# tr...:
TRANS_RE = re.compile(r'\s*tr.*?:\s*(.*)')
# Default feature agreements for different categories
DFLTAGRS_RE = re.compile(r'\s*dfltagrs*?:\s*(.*)')
# Beginning of feature-value list
FEATS_RE = re.compile(r'\s*feat.*?:\s*(.*)')
# Feature-value pair
FV_RE = re.compile(r'\s*(.*?)\s*=\s*(.*)')
# FV combinations, could be preceded by ! (= priority)
FVS_RE = re.compile(r'([!]*)\s*([^!]*)')
# Abbrev, with prefixes, and full name
ABBREV_NAME_RE = re.compile(r'([*%]*?)([^*%()]*?)\s*\((.*)\)\s*(\[.*\])?')
NAME_RE = re.compile(r'([*%]*)([^*%\[\]]*)\s*(\[.*\])?')
# Feature to be recorded in anal output; new 2015.03.10
# xf: g gender
# xf~: VOS voseo
EXPL_FEAT_RE = re.compile(r'\s*xf(.*):\s*(.*)\s*=\s*(.*)')
# Preprocessing: replace characters in first list with last char
# clean: â, ä = ã
CLEAN_RE = re.compile(r'\s*cle.*?:\s*(.*)\s*=\s*(.*)')
# postprocessing: ĝ = g̃
VOWEL_RE = re.compile(r'\s*vow.*?:\s*(.*)')
CONS_RE = re.compile(r'\s*cons.*?:\s*(.*)')
GEM_RE = re.compile(r'\s*gem.*?:\s*(.*)')
POSTPROC_RE = re.compile(r'\s*postproc:\s*(.*)\s*=\s*(.*)')
POSTSYLL_RE = re.compile(r'\s*postsyll.*?:\s*(.*)')
POSTPUNC_RE = re.compile(r'\s*postpunc.*?:\s*(.*)')
# Features to be ignored during generation
DELFEAT_RE = re.compile(r'\s*delfeats:\s*(.*)')
# POS conversion
POSCONV_RE = re.compile(r'\s*posconv:\s*(.*)')
# feature conversion
FEATCONV_RE = re.compile(r'\s*featconv:\s*(.*)')
# feature copying
FEATCOPY_RE = re.compile(r'\s*featcopy:\s*(.*)')

## Regex for checking for non-ascii characters
ASCII_RE = re.compile(r'[a-zA-Z]')

## Separates Morphosyn name from pattern and other attributes
MS_NAME_SEP = '::'
JOIN_NAME_SEP = '::'

## Constants for language use
ANALYSIS = 0
GENERATION = 1
# translation
SOURCE = 2
TARGET = 3
# training target; both analysis and generation
BIDIR = 4

## Strings used in groups file
GROUP_SEP = '**'
TRANS_START = '->'
HEAD_SEP = ';'
# separates alternative source group tokens
ALT_SEP = '|'

## Default end-of-sentence characters
EOS = '.!?'

class Language:
    """
    Dictionaries of words, lexemes, grammatical features, and lexical classes.
    """

    class_char = '$'
    pattern_char = '/'

    languages = {}

    # Regular expressions for affix files
    pattern = re.compile('\s*pat.*:\s+(\w+)\s+(.+)')
    function = re.compile('\s*func.*:\s+(\w+)\s+(.+)')
    suffix = re.compile('\s*suf.*:\s+(\S+)(\s.+)?')   # a single space separates the suffix from the segmented form
    grammar = re.compile('\s*gram.*:\s+(\w+)\s+(.+)')
    POS = re.compile('\s*pos:\s+(\w+)')
    # Regular expressions for identifying token types
    # optional ,|. + at least one digit + optional [,.digit]s; note: allows
    # expression to end with . or ,
    numeral = re.compile("[,.]?\d+[\d.,]*$")
    geez_numeral = re.compile("[፩፪፫፬፭፮፯፰፱፻፲፳፴፵፶፷፸፹፺፼]+$")

    # Regular expressions for join files
    joingrp = re.compile('\s*>>\s*(.*)')

    def __init__(self, name, abbrev, use=ANALYSIS,
                 # A directory may be provided.
                 directory=None,
                 # When an external tagger is used, these are read in from the .lg file
                 # exttag: source|spec
                 # conversion: (POS_tag_conversion_dict, feature_conversion_dict)
                 exttag=False, conversion=False,
                 # list of POS tags with POS collocations to be read in
                 collocs=None,
                 # list of morphological features to help with target disambiguation
                 disambig_feats=None,
                 # list of lists of morphological features that should agree within a sentence
                 disambig_agree=None,
                 # penalties for None/False/0 morphology values
                 disambig_penalties=None,
#                 lemmas=None,
                 # phrases to be joined during sentence tokenization
                 mwe=False,
                 # end-of-sentence characters
                 eos=EOS,
                 # list of lists of POS tags for group grouping
                 groupcats=None,
                 # Added from morphology/language
                 pos=None, cache=True,
                 postags=None, namejoin=None,
                 # Whether this language uses Geez orthography
                 geez=False):
        """Initialize dictionaries and names."""
        self.name = name
        self.abbrev = abbrev
        # Whether to load POS tagger for this language (from elsewhere)
        self.exttag = exttag
        # Phrases to join during sentence tokenization
        self.mwe = mwe
        # Words that can join names
        self.namejoin = namejoin
        # Groups organized by POS or other categories; used to create a list of group dicts for
        # each sublist in groupcats; by default (always?) there are two sublists
        self.groupcats = groupcats
        self.groups = [{} for g in range(len(groupcats))] if groupcats else [{}]
        # Source-ambiguous groups (like ir|ser in Spanish), with associated unambiguous groups
        # (like ser and ir).
        self.sambig_groups = {}
        # A dictionary of group attribute defaults for different head categories
        self.group_defaults = {}
        # Dictionary of roots/stems/tokens to group keys, e.g., 'drop': ['drop_n', 'drop_v']
        self.group_keys = {}
        # Dict of POS tag conversions
        self.postags = postags or {}
        # Candidate groups from training; added 2017.3.6
        self.cand_groups = {}
        # Morphosyns
        self.ms = []
        # Joins
        self.join_groupings = []
        self.eos = eos
        self.use = use
        # Dict of groups with names as keys
        self.groupnames = {}
        # Record whether language has changed since last loaded
        self.changed = False
        # Add to the dictionary of loaded languages.
        Language.languages[abbrev] = self
        # Set the directory where data is
        self.directory = directory or os.path.join(LANGUAGE_DIR, abbrev)
        ## 2015.5.15 Copied from morphology/language
        self.pos = pos or []
        # Dictionary of preprocessing character conversions
        self.clean = {}
        # Dictionary of postprocessing character conversions
        self.postproc = {}
        # Dictionary of postprocessing punctuation conversions
        self.postpunc = {}
        # Vowels, consonants, gemination character, and conversion dict needed for postprocessing for syllabaries
        self.vowels = []
        self.consonants = []
        self.gem_char = '_'
        self.postsyll = {}
        # Dictionary of suffixes and suffix sequences and what to do with them
        self.suffixes = {}
        self.accent = None
        self.deaccent = None
        # Dictionary of prefixes and prefix sequences and what to do with them
        self.prefixes = {}
        self.punc = None
        # Character and character sequences representing orthographic units
        self.seg_units = None
        # Default feature agreements for POS categories
        self.dfltagrs = {}
        # dict of POS: fst lists
        self.morphology = Morphology()
        self.morphology.directory = self.get_dir()
        self.morphology.language = self
        self.load_morpho_data()
        # Whether morphological data is loaded
        self.anal_loaded = False
        self.gen_loaded = False
        # All known morphologically simple words
        self.words = []
        # Categories (and other semantic features) of words and roots; word->cats dict
        self.cats = {}
        self.tokenPOS = {}
        self.read_cats()
        # 2019.9.8: POS tags associated with collocations
        if collocs:
            self.read_collocs(collocs)
        else:
            self.collocs = None
        # 2019.11
        self.disambig_feats = disambig_feats
        self.disambig_agree = disambig_agree
        self.disambig_penalties = disambig_penalties
        # Classes used in identifying numerals, etc.; class->words dict
        self.classes = {}
        # Patterns consisting of explicit tokens, classes, and patterns; used in identifying numerals, etc.
        self.patterns = {}
        self.pattern_list = []
        # Direct translation patterns
        self.translations = {}
        # List of abbreviations (needed for tokenization)
        self.abbrevs = []
        self.read_abbrevs()
        # Translation counts
        self.transcounts = {}
        # Segmentation dicts
        self.segs = {}
        self.rev_segs = {}
        self.read_segs()
        # Lexical exceptions
        self.exceptions = []
        self.load_exceptions()
        # Cached entries read in when language is loaded if language will be used for analysis
        # Disambig dicts also created
        self.POSambig = {}
        self.lexambig = {}
        if use in (ANALYSIS, SOURCE, BIDIR):
            self.set_anal_cached()
        # Load groups now if not to be used for translation
        if use in (ANALYSIS,):
            self.read_groups()
        # Load POS tagger from NLTK or Spacy if called for for this language
        if exttag:
            print("Loading external tagger...")
            source, arg = exttag.split("|")
            import iwqet.tag as tag
#            if lemmas:
#                lemmas = self.read_lemmas()
            self.tagger = tag.get_tagger(source, arg, self.abbrev,
                                         conversion=conversion,
#                                         lemmas=lemmas,
                                         eos=self.eos)
        else:
            self.tagger = None
        if not exttag or self.tagger.morph:
            generate = use in (GENERATION, TARGET, BIDIR)
            analyze = use in (ANALYSIS, SOURCE, BIDIR)
            self.load_morpho(generate=generate,analyze=analyze,
                             segment=False, guess=analyze,
                             verbose=False)
        self.orthographize = None
        self.romanize = None
        self.upper = True
        if geez:
            self.enable_geez()
#        print("Lengua {} creada".format(self))

    ### Characters, orthography

    def enable_geez(self):
        """
        Enable Geez orthography for this language.
        """
        self.orthographize = lambda x: geezify(x, lang=self.abbrev)
        self.romanize = lambda x: romanize(x, lang=self.abbrev)
        self.geez = True
        self.upper = False

    def is_dig_numeral(self, string):
        if self.geez:
            if Language.geez_numeral.match(string):
                return True
        elif Language.numeral.match(string):
            return True
        return False

    @staticmethod
    def is_currency(string):
        if string[0] in "$£€¥₲":
            if Language.is_dig_numeral(string[1:]):
                return True
        return False

    @staticmethod
    def is_class(string):
        return string and string[0] == Language.class_char

    @staticmethod
    def is_pattern(string):
        return string and string[0] == Language.pattern_char

    def match_pattern_item(self, item, word):
        """Item may be a set of alternatives, a class, or a word."""
        if isinstance(item, set):
            return self.match_set(item, word)
        elif Language.is_class(item):
            return self.match_class(item, word)
        else:
            return item == word

    def match_set(self, items, word):
        return any([self.match_pattern_item(i, word) for i in items])

    def match_class(self, cls, word):
        """
        Does word match class (either a string beginning with class_char
        or a list of class elements)?
        """
        if isinstance(cls, str):
            cls = self.classes.get(cls)
        for item in cls:
            if Language.is_class(item):
                if self.match_class(item, word):
                    return True
            elif item == word:
                return True
        return False

    def match_pattern(self, pattern, words, verbose=False):
        """
        Determine if pattern (a string beginning with pattern_char or a
        pattern list), matches beginning of list of words.
        If so, return the index of the word following the match.
        """
        if verbose:
            print("Matching pattern {} with words {}".format(pattern, words))
        if isinstance(words, str):
            words = words.split()
        if isinstance(pattern, str):
            pattern = self.patterns.get(pattern)
        if not pattern:
            return False
        if isinstance(pattern, set):
            if self.match_set(pattern, words[0]):
                return words[0], 1
            else:
                return False
        match_words = words
        word_position = 0
        pattern_position = 0
        matched = []
        while word_position < len(words) and pattern_position < len(pattern):
            if verbose:
                print("  word position {}, pattern position {}".format(word_position, pattern_position))
            match_words = words[word_position:]
            pattern_item = pattern[pattern_position]
            if Language.is_pattern(pattern_item):
                mp = self.match_pattern(pattern_item, words[word_position:])
                if mp:
                    new_matched, new_pos = mp
                    # pattern within pattern matches
                    pattern_position += 1
                    matched.extend(new_matched)
                    word_position += new_pos
                else:
                    return False
            else:
                mpi = self.match_pattern_item(pattern_item, match_words[0])
                if mpi:
                    word_position += 1
                    pattern_position += 1
                    matched.append(match_words[0])
                else:
                    return False
        return matched, word_position

    def get_num_patterns(self):
        return [p for p in self.pattern_list if '/num' in p[0]]

    def postag_match(self, taggertag, morphotag):
        """Does the POS tag from the tagger match the tag from the morphological analyzer?"""
        if morphotag in self.postags:
            return taggertag in self.postags[morphotag]
        return False

    def is_known(self, token):
        """
        Is the lowercase token a known word, either because it is in the list
        of known words or can be analyzed by the morphological analyzer?
        """
        if token in self.words:
            return True
        anal = self.anal_word(token)
        if anal[0].get('features'):
            # There is a morphological analysis
            # %% Figure out a way to save this
            return True
        return False

    def find_special(self, words, first=False, inquote=False):
        """Searches for special words in words: digits, names.
        If it does, it returns the list of tokens and the
        special character code for the sequence.
        """
#        print("Finding special in {}".format(words))
        if isinstance(words, str):
            words = words.split()
        # Try to find a digit
        if self.is_dig_numeral(words[0]):
            return [words[0]], 'ND'
        # Try to find a sequence of number words
        for name, pattern in self.get_num_patterns():
            pat_match = self.match_pattern(pattern, words)
            if pat_match:
                numwords = pat_match[0]
                return numwords, 'N'
        # Try to find a sequence of name words
        name = True
        names = []
        # If the language doesn't support capitalization, don't bother
        # looking for names.
        if not self.upper:
            return False
        while name and words:
            word = words.pop(0)
            if len(word) == 0:
                name = False
                break
            elif word[0].isupper():
                # Word is capitalized
                lowered = word.lower()
                lowered_known = self.is_known(lowered)
                if first:
                    # In first position, check if it's known in one of its forms
                    cap = lowered.capitalize()
                    # Give priority to known name
                    if self.is_known(cap):
                        names.append(word)
                    elif lowered_known:
                        name = False
                        break
                    else:
                        names.append(word)
                elif SentToken.is_name_token(word):
                    # A name=like token in other than first position
                    if inquote or (words[-1] in ['', '¶'] and not names):
                        # No end punctuation and no previous special words
                        if lowered_known:
                            name = False
                            break
                        else:
                            names.append(word)
                    else:
                        names.append(word)
                elif word.isupper() and lowered_known:
                    name = False
                    break
                else:
                    names.append(word)
            elif names and word in self.namejoin and any([SentToken.is_name_token(w) for w in words[:2]]):
                # Namejoin token, like 'y'; can only precede some capitalized word
                names.append(word)
            else:
                # End of name sequence
                name = False
                break
        if names:
            return names, 'C'
        return False

    def quit(self, cache=True):
        """Do stuff when the program exits. Only cache analyses and generation if there is a current
        session/user."""
        if cache and self.use in (GENERATION, TARGET, BIDIR):
            for pos in self.morphology.values():
                pos.quit()

    def __repr__(self):
        """Print name."""
        return '<<{}>>'.format(self.name)

    def is_punc(self, string):
        """Does the string consist of only punctuation characters?"""
        for char in string:
            if char not in self.morphology.punctuation:
                return False
        return True

    def ortho_clean(self, string):
        """Clean up orthographic variability."""
        for c, d in self.clean.items():
            if c in string:
                string = string.replace(c, d)
        return string

    ### Getting and setting
    def get_group(self, name, key=None, posindex=0):
        """Name if not None is a string representing the group's 'name'."""
        key = key or Group.get_key(name)
        cands = self.groups[posindex].get(key)
        if cands:
            return firsttrue(lambda c: c.name == name, cands)
        return None

#    # Simple (purely lexical) and complex (lexical + syntactic) groups
#    def get_simple_groups(self):
#        return self.groups[0]
#
#    get_lex_groups = get_simple_groups
#
#    def get_complex_groups(self):
#        return self.groups[1]
#
#    get_syn_groups = get_complex_groups

    def get_from_MWEs(self, tokens, mwes=None):
        """
        If list of tokens is in tree, return the leaf (its POS).
        Otherwise return False.
        """
        if not mwes:
            mwes = self.mwe
        if not tokens or not mwes:
            return False
        next_token = tokens.pop(0)
        if next_token in mwes:
            new_mwes = mwes[next_token]
            if '' in new_mwes:
                # End of tree is one possibility; return POS if this is the end of tokens
                if not tokens:
                    return new_mwes['']
                elif len(new_mwes) > 1:
                    # There are other longer options though
                    return self.get_from_MWEs(tokens, new_mwes)
                else:
                    return False
            else:
                return self.get_from_MWEs(tokens, new_mwes)
        else:
            return False

    ### Directories and files

    @staticmethod
    def get_language_dir(abbrev):
        return os.path.join(LANGUAGE_DIR, abbrev)

    @staticmethod
    def get_mwe_file(lg_abbrev, name='1'):
        d = Language.get_language_dir(lg_abbrev)
        return os.path.join(os.path.join(d, 'lex'), name + ".mwe")

    def get_dir(self):
        """Where data for this language is kept."""
        return os.path.join(LANGUAGE_DIR, self.abbrev)

    def get_syn_dir(self):
        """Directory for .ms (MorphoSyn) files (at least)."""
        return os.path.join(self.directory, 'syn')

    def get_fst_dir(self):
        return os.path.join(self.directory, 'fst')

    def get_lex_dir(self):
        return os.path.join(self.directory, 'lex')

    def get_cache_dir(self):
        """Directory with cached analyses."""
        return os.path.join(self.directory, 'cache')

    def get_group_dir(self):
        """Directory with group files."""
        return os.path.join(self.directory, 'grp')

    def get_data_dir(self):
        """Data directory: documents and their translations."""
        return os.path.join(self.directory, 'data')

    def get_stat_dir(self):
        """Data directory: corpus and corpus analyses."""
        return os.path.join(self.directory, 'stat')

    def get_pseudoseg_file(self, filename):
        return os.path.join(self.get_data_dir(), filename + '.ps')

    def get_transcount_file(self, language):
        return os.path.join(self.get_stat_dir(), language + '.tc')

    def get_colloc_file(self, tag):
        return os.path.join(self.get_syn_dir(), tag + '.cloc')

    def get_ms_file(self, target_abbrev):
        d = self.get_syn_dir()
        return os.path.join(d, target_abbrev + '.ms')

    def get_join_file(self, target_abbrev):
        d = self.get_syn_dir()
        return os.path.join(d, target_abbrev + '.jn')

    def get_cache_file(self, name=''):
        d = self.get_cache_dir()
        if name == True or not name:
            name = self.abbrev
        return os.path.join(d, name + '.cch')

    def get_sem_file(self, name=''):
        d = self.get_lex_dir()
        if name == True or not name:
            name = 'sem'
        return os.path.join(d, name + '.lex')

    def get_abbrev_file(self, name=''):
        d = self.get_lex_dir()
        if name == True or not name:
            name = 'abr'
        return os.path.join(d, name + '.lex')

    def get_group_files(self, names=None):
        d = self.get_group_dir()
        if not names:
            if self.groupcats:
                names = reduce_lists(self.groupcats)
            elif self.morphology:
                # POS abbreviations
                names = ['misc', 'nm'] + list(self.morphology.keys())
            else:
                names = [self.abbrev]
        namepaths = [(name, os.path.join(d, name + '.grp')) for name in names]
        return [(name, path) for name, path in namepaths if os.path.exists(path)]

    def get_grouplist_files(self, names=None):
        d = self.get_group_dir()
        if self.groupcats:
            # A list of lists of POS labels
            namegroups = self.groupcats
        else:
            namegroups = [list(self.morphology.keys())]
        namepaths = [[(name, os.path.join(d, name + '.grp')) for name in names] for names in namegroups]
        # Doesn't check whether paths exist
        return namepaths

    def get_cat_group_file(self, cat):
        """Get the path for the group file for cat."""
        d = self.get_group_dir()
        path = os.path.join(d, cat + '.grp')
        if os.path.exists(path):
            return path

    def get_seg_file(self):
        """Pathname for file containing segmentable forms, e.g., del, they're."""
        d = self.get_lex_dir()
        return os.path.join(d, 'seg.lex')

    def set_anal_cached(self):
        self.cached = {}
        self.read_cache(expand=True)
        # New analyses since language loaded,
        # each entry a wordform and list of (root, FS) analyses
        self.new_anals = {}

    def add_new_anal(self, word, anals):
        self.new_anals[word] = anals

    def read_collocs(self, tags):
        collocs = {}
        for tag in tags:
            try:
                with open(self.get_colloc_file(tag), encoding='utf8') as f:
                    pre = []
                    post = []
                    in_pre = True
                    for line in f:
                        line = line.strip()
                        if not line:
                            in_pre = False
                            continue
                        line = line.split()
                        if in_pre:
                            pre.append(line)
                        else:
                            post.append(line)
                collocs[tag] = pre, post
            except IOError:
                print("No file found the category {}".format(tag))
        self.collocs = collocs

    def read_cats(self):
        file = self.get_sem_file()
        try:
            with open(file, encoding='utf8') as f:
                for line in f:
                    form, sem = line.strip().split()
                    raw = form.split('_')[0]
                    cats = sem.split(',')
                    self.cats[form] = cats
                    if '_' in form:
                        POS = form.split('_')[1]
                        self.tokenPOS[raw] = POS
                    self.words.append(raw)
        except IOError:
            pass

    def read_transcounts(self, language):
        try:
            with open(self.get_transcount_file(language), encoding='utf8') as file:
                for line in file:
                    head, translations = line.split("::")
                    head = head.strip()
                    self.transcounts[head] = eval(translations)
        except IOError:
            print("No transcount file for {}".format(language))

    def get_cats(self, form):
        return self.cats.get(form, [])

    def read_abbrevs(self):
        """Read in abbreviations from abr file."""
        file = self.get_abbrev_file()
        try:
            with open(file, encoding='utf8') as f:
                for line in f:
                    self.abbrevs.append(line.strip())
        except IOError:
            pass

    def read_segs(self):
        """Read in segmentations from seg file."""
        file = self.get_seg_file()
        try:
            with open(file, encoding='utf8') as f:
                for line in f:
                    if not line or '=' not in line:
                        print("Error: segmentation file line {} must contain '='".format(line.strip()))
                    form, seg = line.split('=')
                    form = form.strip()
                    seg = seg.strip()
                    self.segs[form] = seg.split()
                    self.rev_segs[seg] = form
        except IOError:
            pass

    def write_cache(self, name=''):
        """Write a dictionary of cached entries to a cache file."""
        if self.new_anals:
            # Only attempt to cache analyses if there are new ones.
            file = self.get_cache_file(name=name)
            with open(file, 'a', encoding='utf8') as out:
                for word, analyses in self.new_anals.items():
                    if not analyses:
                        # The word is unanalyzed
                        print("{} || {}:".format(word, word), file=out)
                    # analyses is a list of root, fs pairs
                    else:
                        anals = ["{}:{}".format(r, f.__repr__() if f else '') for r, f in analyses]
                        anals = ';;'.join(anals)
                        print("{} || {}".format(word, anals), file=out)
        # Empty new_anals in case we want to add things later
        self.new_anals.clear()

    def read_cache(self, name='', expand=False, verbose=False):
        """Read cached entries into self.cached from a file.
        Modified 2015/5/17 to include Mbojereha categories.
        Modified a lot 2019.9.8: need to clean up."""
        cache = self.get_cache_file(name=name)
        try:
            with open(cache, encoding='utf8') as f:
                 for line in f:
                    split_line = line.strip().split(" || ")
                    word, analyses = split_line
                    analyses = analyses.split(';;')
                    anals = [a.split(':') for a in analyses]
                    alist = []
#                    print("word {}, anals {}".format(word, anals))
                    if any([(len(anal) != 2) for anal in anals]):
                        print("Problem with cache entry {}".format(line))
                    for r, a in anals:
                        if expand and a:
                            a = FSSet(a)
                        alist.append({'root': r, 'features': a})
                    POSs = set()
                    roots = set()
                    POSd = {}
                    for al in alist:
                        feats = al['features']
                        root = al['root']
                        roots.add(root)
                        if feats:
                            POS = feats.get('pos')
                        elif word in self.tokenPOS:
                            POS = self.tokenPOS[word]
                            al['pos'] = POS
                        if POS:
                            # THIS IS ALL SPANISH-SPECIFIC SO SHOULDN'T BE HERE
                            if POS == 'v':
                                if feats.get('fin'):
                                    POS = 'v.fin'
                                else:
                                    tm = feats.get('tm')
                                    if tm == 'prc':
                                        POS = 'v.prc'
                                    elif tm == 'inf':
                                        POS = 'v.inf'
                                    else:
                                        POS = 'v.ger'
                            POSs.add(POS)
                            if POS in POSd:
                                POSd[POS].append(al)
                            else:
                                POSd[POS] = [al]
                            # Add POS tag to root; later do this in .cch file
                            al['root'] = "{}_{}".format(root, POS.split('.')[0])
                    if len(POSs) >= 2:
                        self.POSambig[word] = POSd
                    if len(roots) >= 2:
                        self.lexambig[word] = alist
#                    if len(POSs) < 2 and len(roots) < 2:
#                        print("{} {} neither POS nor lex ambiguous".format(word, analyses))
                    if not expand:
                        # Put False at the front of the list to show that it hasn't been expanded
                        alist.insert(0, False)
                    self.cached[word] = alist
        except IOError:
            if verbose:
                print('No such cache file as {}'.format(cache))

    def get_cached_anal(self, word, expand=False):
        """
        Return a list of dicts, one for each analysis of the word, or None.
        """
        entries = self.cached.get(word, None)
        if entries and expand and entries[0] is False:
            for entry in entries[1:]:
                feat = entry.get('features')
                if feat:
                    entry['features'] = FSSet.parse(entry['features'])
                    pos = entry['features'].get('pos', '')
                    entry['root'] = Language.make_root(entry['root'], pos)
            self.cached[word] = entries[1:]
            return copy.deepcopy(entries[1:])
        return copy.deepcopy(entries)

    ## Functions for creating and search word trees (for phrases that are joined in tokenizing).

    @staticmethod
    def treeify(phrases, tree=None):
        """
        Create a word tree (a dict of dicts) for phrases, where each phrase
        is a (list_of_strings, tag) pair.
        """
        if len(phrases) == 0:
            return ''
        if isinstance(phrases, str):
            return phrases
        if not tree:
            tree = {}
        for phrase, tag in phrases:
            if not phrase:
                tree[''] = tag
                continue
            start, rest = phrase[0], phrase[1:]
            if start in tree:
                tree[start].append((rest, tag))
            else:
                tree[start] = [(phrase[1:], tag)]
        for start, rests in tree.items():
            tree[start] = Language.treeify(rests)
        return tree

    @staticmethod
    def make_char_string(chars):
        """Used in making list of seg units for language."""
        non_ascii = []
        for char in chars:
            if not ASCII_RE.match(char):
                non_ascii.append(char)
        non_ascii.sort()
        non_ascii_s = ''.join(non_ascii)
        return r'[a-zA-Z' + non_ascii_s + r']'

    @staticmethod
    def make_seg_units(segs):
        """Convert a list of segments to a seg_units list + dict."""
        singletons = []
        dct = {}
        for seg in segs:
            c0 = seg[0]
            if c0 in dct:
                dct[c0].append(seg)
            else:
                dct[c0] = [seg]
        for c0, segs in dct.items():
            if len(segs) == 1 and len(segs[0]) == 1:
                singletons.append(c0)
        for seg in singletons:
            del dct[seg]
        singletons.sort()
        return [singletons, dct]

    def load_exceptions(self):
        path = os.path.join(self.get_lex_dir(), "excep.lex")
        if not os.path.exists(path):
            return
        with open(path, encoding='utf8') as exc:
            for line in exc:
                if not line or '#' in line:
                    continue
                word = line.strip()
                self.exceptions.append(word)

    def load_morpho_data(self):
        """Load morphological data from .mrf file."""
        path = os.path.join(self.directory, self.abbrev + '.mrf')
        if not os.path.exists(path):
            print("No morphological data for {}".format(self.name))
            return
        print('Loading morphological data for {}'.format(self.name))
        posconv = []
        featconv = []
        featcopy = []
        delfeats = []
        with open(path, encoding='utf8') as data:
            contents = data.read()
            lines = contents.split('\n')[::-1]

            seg = []
            dfltagrs = []
            postsyll = []
            abbrev = {}
            fv_abbrev = {}
            trans = {}
            fv_dependencies = {}
            fv_priorities = {}
            fullpos = {}

            excl = {}
            feats = {}
            lex_feats = {}
            true_explicit = {}
            explicit = {}

            chars = ''

            current = None

            current_feats = []
            current_lex_feats = []
            current_excl = []
            current_abbrev = {}
            current_fv_abbrev = []
            current_fv_priority = []
            current_explicit = []
            current_true_explicit = []
            current_fv_dependencies = {}

            complex_feat = False
            current_feat = None
            current_value_string = ''
            complex_fvs = []

            while lines:

                line = lines.pop().split('#')[0].strip() # strip comments

                # Ignore empty lines
                if not line: continue

                # Beginning of segmentation units
                m = SEG_RE.match(line)
                if m:
                    current = 'seg'
                    seg = m.group(1).split()
                    continue

                # Beginning of default feature agreements
                m = DFLTAGRS_RE.match(line)
                if m:
                    current = 'dfltagrs'
                    continue

                m = VOWEL_RE.match(line)
                if m:
                    vowels = m.group(1).split()
                    self.vowels = vowels
                    continue

                m = CONS_RE.match(line)
                if m:
                    cons = m.group(1).split()
                    self.consonants = cons
                    continue

                m = GEM_RE.match(line)
                if m:
                    gem = m.group(1)
                    self.gem_char = gem
                    continue

                m = ACC_RE.match(line)
                if m:
                    acc = m.group(1).split(',')
                    self.accent = {}
                    for c in acc:
                        u, a = c.split(':')
                        self.accent[u.strip()] = a.strip()
                    continue

                m = DEACC_RE.match(line)
                if m:
                    deacc = m.group(1).split(',')
                    self.deaccent = {}
                    for c in deacc:
                        a, u = c.split(':')
                        self.deaccent[a.strip()] = u.strip()
                    continue

                m = PUNC_RE.match(line)
                if m:
                    self.punc = m.group(1).split()
                    continue

                m = POSTPUNC_RE.match(line)
                if m:
                    pairs = m.group(1).split()
                    for pair in pairs:
                        source, target = pair.split('=')
                        self.postpunc[source] = target
                    continue

                m = DELFEAT_RE.match(line)
                if m:
                    delposfeats = m.group(1).split(';')
                    for delposfeat in delposfeats:
                        delpos, delfeatures = delposfeat.split('::')
                        delpos = delpos.strip()
                        delfeatures = delfeatures.strip().split(',')
                        delfeats.append((delpos, delfeatures))
                    continue

                m = POSCONV_RE.match(line)
                if m:
                    current = 'posconv'
                    continue

                m = FEATCONV_RE.match(line)
                if m:
                    current = 'featconv'
                    continue

                m = FEATCOPY_RE.match(line)
                if m:
                    current = 'featcopy'
                    continue

                m = POSTSYLL_RE.match(line)
                if m:
                    current = 'postsyll'
                    postsyll = m.group(1).split()
                    continue

                m = TRANS_RE.match(line)
                if m:
                    current = 'trans'
                    w_g = m.group(1).split()
                    if '=' in w_g:
                        w, g = w_g.split('=')
                        # Add to the global TDict
                        Language.T.add(w.strip(), g.strip(), self.abbrev)
                    continue

                m = CLEAN_RE.match(line)
                if m:
                    dirty, clean = m.groups()
                    for d in dirty.split(','):
                        d = d.strip()
                        self.clean[d] = clean
                    continue

                m = POSTPROC_RE.match(line)
                if m:
                    dirty, clean = m.groups()
                    for d in dirty.split(','):
                        d = d.strip()
                        self.postproc[d] = clean
                    continue

                m = FEATS_RE.match(line)
                if m:
                    current = 'feats'
                    continue

                if current == 'feats':
                    m = POS_RE.match(line)
                    if m:
                        pos, fullp = m.groups()
                        pos = pos.strip()
                        fullp = fullp.strip()
                        self.pos.append(pos)
                        current_feats = []
                        current_abbrev = {}
                        current_fv_abbrev = []
                        current_fv_priority = []
                        current_explicit = []
                        current_true_explicit = []
                        current_fv_dependencies = {}
                        feats[pos] = current_feats
                        abbrev[pos] = current_abbrev
                        fv_abbrev[pos] = current_fv_abbrev
                        fv_priorities[pos] = current_fv_priority
                        explicit[pos] = current_explicit
                        true_explicit[pos] = current_true_explicit
                        fullpos[pos] = fullp
                        fv_dependencies[pos] = current_fv_dependencies
                        continue

                    m = ABBREV_RE.match(line)
                    if m:
                        abb_sig = m.group(1).strip()
                        if '=' in abb_sig:
                            abb, sig = abb_sig.split('=')
                            current_abbrev[abb.strip()] = sig.strip()
                        continue

                    m = EXPL_FEAT_RE.match(line)
                    # Feature to include in pretty output
                    if m:
                        opt, fshort, flong = m.groups()
                        fshort = fshort.strip()
                        opt = opt.strip()
                        current_abbrev[fshort] = flong.strip()
                        current_explicit.append(fshort)
                        if opt and opt == '~':
                            current_true_explicit.append(fshort)
                        continue

                    m = FV_RE.match(line)
                    if m:
                        # A feature and value specification
                        feat, val = m.groups()
                        if '+' in feat or '-' in feat:
                            # Expansion for a set of boolean feature values
                            # See if there's a ! (=priority) prefix
                            m2 = FVS_RE.match(feat)
                            priority, fvs = m2.groups()
                            # An abbreviation for one or more boolean features with values
                            fvs = fvs.split(',')
                            fvs = [s.strip() for s in fvs]
                            fvs = [s.split('=') if '=' in s else [s[1:], (True if s[0] == '+' else False)] for s in fvs]
                            current_fv_abbrev.append((fvs, val))
                            if priority:
                                current_fv_priority.append(fvs)
                        elif '=' in val:
                            # Complex feature (with nesting)
                            complex_feat = self.proc_feat_string(feat, current_abbrev, current_excl, current_lex_feats,
                                                                 current_fv_dependencies)
                            vals = val.split(';')
                            for fv2 in vals:
                                fv2 = fv2.strip()
                                if fv2:
                                    m2 = FV_RE.match(fv2)
                                    if m2:
                                        feat2, val2 = m2.groups()
                                        f = self.proc_feat_string(feat2, current_abbrev, current_excl, current_lex_feats,
                                                                  current_fv_dependencies)
                                        v = self.proc_value_string(val2, f, current_abbrev, current_excl,
                                                                   current_fv_dependencies)
                                        complex_fvs.append((f, v))
                            if len(vals) == 1:
                                current_feats.append((complex_feat, complex_fvs))
                                complex_feat = None
                                complex_fvs = []

                        else:
                           fvs = line.split(';')
                           if len(fvs) > 1:
                               # More than one feature-value pair (or continuation)
                               if not complex_feat:
                                   complex_feat = current_feat
                               for fv2 in fvs:
                                   fv2 = fv2.strip()
                                   if fv2:
                                       m2 = FV_RE.match(fv2)
                                       if m2:
                                           # A single feature-value pair
                                           feat2, val2 = m2.groups()
                                           f = self.proc_feat_string(feat2, current_abbrev, current_excl, current_lex_feats,
                                                                     current_fv_dependencies)
                                           v = self.proc_value_string(val2, f, current_abbrev, current_excl,
                                                                      current_fv_dependencies)
                                           complex_fvs.append((f, v))
                           elif complex_feat:
                               # A single feature-value pair
                               f = self.proc_feat_string(feat, current_abbrev, current_excl, current_lex_feats,
                                                         current_fv_dependencies)
                               v = self.proc_value_string(val, f, current_abbrev, current_excl,
                                                          current_fv_dependencies)
                               complex_fvs.append((f, v))
                               current_feats.append((complex_feat, complex_fvs))
                               complex_feat = None
                               complex_fvs = []
                           else:
                               # Not a complex feature
                               current_feat = self.proc_feat_string(feat, current_abbrev, current_excl, current_lex_feats,
                                                                    current_fv_dependencies)
                               current_value_string = ''
                               val = val.strip()
                               if val:
                                   # The value is on this line
                                   # Split the value by |
                                   vals = val.split('|')
                                   vals_end = vals[-1].strip()
                                   if not vals_end:
                                       # The line ends with | so the value continues
                                       current_value_string = val
                                   else:
                                       v = self.proc_value_string(val, current_feat, current_abbrev, current_excl,
                                                                  current_fv_dependencies)
                                       current_feats.append((current_feat, v))
                    else:
                        # Just a value
                        val = line.strip()
                        current_value_string += val
                        # Split the value by | to see if it continues
                        vals = val.split('|')
                        if vals[-1].strip():
                            v = self.proc_value_string(current_value_string, current_feat, current_abbrev, current_excl,
                                                       current_fv_dependencies)
                            current_feats.append((current_feat, v))
                            current_value_string = ''

                elif current == 'seg':
                    seg.extend(line.strip().split())

                elif current == 'posconv':
                    posconv.append(line.strip().split('::'))

                elif current == 'featconv':
                    featconv.append(line.strip().split('::'))

                elif current == 'featcopy':
                    featcopy.append(line.strip().split('::'))

                elif current == 'dfltagrs':
                    dfltagrs.append(line.strip().split('::'))

                elif current == 'pos':
                    pos.extend(line.strip().split())

                elif current == 'postsyll':
                    postsyll.extend(line.strip().split())

                elif current == 'trans':
                    wd, gls = line.strip().split('=')
                    # Add to the global TDict

                else:
                    print("Warning: can't interpret line in .mrf file: {}".format(line))

            if postsyll:
                # Make postsyll pairs into a dict
                for pair in postsyll:
                    if len(pair.split('=')) != 2:
                        print(pair)
                    roman, native = pair.split('=')
                    self.postsyll[roman] = native

            if seg:
                # Make a bracketed string of character ranges and other characters
                # to use for re
                chars = ''.join(set(''.join(seg)))
                chars = Language.make_char_string(chars)
                # Make the seg_units list, [chars, char_dict], expected for transduction,
                # composition, etc.
                self.seg_units = Language.make_seg_units(seg)


            if dfltagrs:
                for pos, agrs in dfltagrs:
                    self.dfltagrs[pos] = agrs

        if self.pos and not self.morphology:
            for p in self.pos:
                self.morphology[p] = POS(p, self, fullname=fullpos[p])
                self.morphology[p].abbrevs = abbrev[p]
                self.morphology[p].fv_abbrevs = fv_abbrev[p]
                self.morphology[p].fv_priority = fv_priorities[p]
                self.morphology[p].true_explicit_feats = true_explicit[p]
                self.morphology[p].explicit_feats = explicit[p]
                self.morphology[p].feat_list = feats[p]
                self.morphology[p].make_rev_abbrevs()

        if delfeats:
            # Assign delfeats to POS instances
            for pos, feats in delfeats:
                self.morphology[pos].delfeats = feats

        if featconv:
            for pos, fc in featconv:
                # there may be more than one POS separated by |
                for p in pos.split('|'):
                    P = self.morphology[p]
                    fcdict = P.featconv
                    targ, ffcc = fc.split(':')
                    targ = targ.strip()
                    if targ not in fcdict:
                        fcdict[targ] = []
        #                    fcdict[targ] = []
                    for fffccc in ffcc.strip().split(';'):
                        if not fffccc:
                            continue
                        conds, targfeats = fffccc.split('->')
                        conds = FeatStruct("[{}]".format(conds.strip()))
                        targfeats = FeatStruct("[{}]".format(targfeats.strip()))
                        fcdict[targ].append((conds, targfeats))

        if featcopy:
            for pos, fc in featcopy:
                P = self.morphology[pos]
                fcdict = P.featcopy
                targ, ffcc = fc.split(':')
                targ = targ.strip()
                if targ not in fcdict:
                    fcdict[targ] = []
#                    fcdict[targ] = []
                fcdict[targ].extend([f.strip() for f in ffcc.split(',')])

        if posconv:
            for pos, pc in posconv:
                P = self.morphology[pos]
                pcdict = P.posconv
                targ, ppcc = pc.split(':')
                targ = targ.strip()
                if targ not in pcdict:
                    pcdict[targ] = []
                for pppccc in ppcc.strip().split(';'):
                    conds, tposfeats = pppccc.split('->')
                    conds = FeatStruct("[{}]".format(conds.strip()))
                    tposfeats = tposfeats.strip().split(',')
                    tpos = tposfeats[0]
                    tfeats = tposfeats[1] if len(tposfeats) == 2 else ''
                    if tfeats:
                        tfeats = FeatStruct("[{}]".format(tfeats))
                    pcdict[targ].append((conds, tpos, tfeats))

    def proc_feat_string(self, feat, abbrev_dict, excl_values, lex_feats, fv_dependencies):
        prefix = ''
        depend = None
        m = ABBREV_NAME_RE.match(feat)

        if m:
            prefix, feat, name, depend = m.groups()
            abbrev_dict[feat] = name
        else:
            m = NAME_RE.match(feat)
            prefix, feat, depend = m.groups()

        # * means that the feature's values are not reported in analysis output
        if '*' in prefix:
            excl_values.append(feat)
        # % means that the feature is lexical
        if '%' in prefix:
            lex_feats.append(feat)

        if depend:
            # Feature and value that this feature value depends on
            # Get rid of the []
            depend = depend[1:-1]
            # Can be a comma-separated list of features
            depends = depend.split(',')
            for index, dep in enumerate(depends):
                dep_fvs = [fvs.strip() for fvs in dep.split()]
                if dep_fvs[-1] == 'False':
                    dep_fvs[-1] = False
                elif dep_fvs[-1] == 'True':
                    dep_fvs[-1] = True
                elif dep_fvs[-1] == 'None':
                    dep_fvs[-1] = None
                depends[index] = dep_fvs
            fv_dependencies[feat] = depends

        return feat

    def proc_value_string(self, value_string, feat, abbrev_dict, excl_values, fv_dependencies):
        '''value_string is a string containing values separated by |.'''
        values = [v.strip() for v in value_string.split('|')]
        res = []
        prefix = ''
        for value in values:
            if not value:
                continue
            if value == '+-':
                res.extend([True, False])
            else:
                m = ABBREV_NAME_RE.match(value)
                if m:
                    prefix, value, name, depend = m.groups()
                    abbrev_dict[value] = name
                else:
                    m = NAME_RE.match(value)
                    prefix, value, depend = m.groups()

                value = value.strip()

                if value == 'False':
                    value = False
                elif value == 'True':
                    value = True
                elif value == 'None':
                    value = None
                elif value == '...':
                    value = FeatStruct('[]')
                elif value.isdigit():
                    value = int(value)

                if '*' in prefix:
                    excl_values.append((feat, value))

                if depend:
                    # Feature and value that this feature value depends on
                    depend = depend[1:-1]
                    dep_fvs = [fvs.strip() for fvs in depend.split()]
                    if dep_fvs[-1] == 'False':
                        dep_fvs[-1] = False
                    elif dep_fvs[-1] == 'True':
                        dep_fvs[-1] = True
                    elif dep_fvs[-1] == 'None':
                        dep_fvs[-1] = None
                    elif dep_fvs[-1] == '...':
                        dep_fvs[-1] = FeatStruct('[]')
                    fv_dependencies[(feat, value)] = dep_fvs

                res.append(value)
        return tuple(res)

    def load_morpho(self, generate=False, analyze=True, segment=False,
                    guess=True, verbose=False):
        """
        Load words and FSTs for morphological analysis and/or generation.
        """
        if verbose:
            print('Loading morphological data for {} (anal:{}, gen:{})'.format(self.name, analyze, generate))
        # Load pre-analyzed words
        self.set_analyzed()
        if analyze:
            self.set_suffixes(verbose=verbose)
        self.morphology.set_words()
        for pos in self.morphology:
            posmorph = self.morphology[pos]
            # Load pre-analyzed words if any
            posmorph.set_analyzed()
            if generate:
                posmorph.read_gen_cache()
            # Load FST
            if generate:
                posmorph.load_fst(generate=True, guess=guess, segment=segment,
                                  verbose=verbose)
                # Load statistics for generation
                posmorph.set_root_freqs()
                posmorph.set_feat_freqs()
            if analyze:
                posmorph.load_fst(generate=False, guess=guess, segment=segment,
                                  verbose=verbose)
            # Do others later
        if generate:
            self.gen_loaded = True
        if analyze:
            self.anal_loaded = True

        return True

    def load_gen(self, verbose=False):
        """Just load the generation FSTs."""
        if self.gen_loaded:
            return
        print('Loading morphological generation data for {}'.format(self.name))
        self.gen_loaded = True
        for pos in self.morphology:
            self.morphology[pos].make_generated()
            # Load FST
            self.morphology[pos].load_fst(generate=True, guess=False, segment=False,
                                          verbose=verbose)

    def set_analyzed(self, filename='analyzed.lex', verbose=False):
        '''
        Set the dict of analyzed words, reading them in from a file,
        one per line.
        '''
        path = os.path.join(self.get_lex_dir(), filename)
        if os.path.exists(path):
            file = open(path, encoding='utf8')
            if verbose:
                print('Storing pre-analyzed forms')
            for line in file:
                # Word and FS separated by two spaces
                word, anal = line.split('  ')
                fs = FSSet.parse(anal.strip())
                self.analyzed[word] = fs
            file.close()

    def set_suffixes(self, filename='suf.lex', verbose=False):
        '''Set the dict of suffixes that can be stripped off.'''
        path = os.path.join(self.get_lex_dir(), filename)
        if os.path.exists(path):
            if verbose:
                print("Loading suffixes from {}".format(path))

            # Make 'v' the default POS
            current_pos = 'v'
            current_suffix = None
            current_attribs = None
            functions = {}
            patterns = {}
            grams = {}

            with open(path, encoding='utf8') as file:
                for line in file:
                    line = line.split('#')[0].strip() # strip comments

                    if not line:
                        continue

                    m = Language.pattern.match(line)
                    if m:
                        patname = m.group(1)
                        regex = m.group(2)
                        patterns[patname] = re.compile(regex)
                        continue
                    m = Language.POS.match(line)
                    if m:
                        current_pos = m.group(1)
                        continue
                    m = Language.grammar.match(line)
                    if m:
                        gname = m.group(1)
                        fs = m.group(2)
                        grams[gname] = FSSet.parse(fs)
                        continue
                    m = Language.function.match(line)
                    if m:
                        name = m.group(1)
                        args = m.group(2)
                        lg_arg = "lg=self, "
                        curry = "iwqet.morphology.strip.sub_curry("
                        call = curry + lg_arg + args + ")"
                        function = eval(call)
                        functions[name] = function
                        continue
                    m = Language.suffix.match(line)
                    if m:
                        if current_suffix:
                            if current_suffix in self.suffixes:
                                self.suffixes[current_suffix].extend(current_attribs)
                            else:
                                self.suffixes[current_suffix] = current_attribs
                        current_suffix = m.group(1)
                        current_attribs = m.group(2)
                        if current_attribs:
                            current_attribs = [current_attribs.strip()]
                        else:
                            current_attribs = []
                        continue
                    if current_suffix:
                        # This line represents a dict of suffix attribs for a particular case
                        # ; separate different attribs
                        attrib_dict = {}
                        suff_attribs = line.split(';')
                        for attrib in suff_attribs:
                            # We need partition instead of split because there
                            # can be other = to the right in a feature-value expression
                            typ, x, value = attrib.strip().partition('=')
                            if typ == 'pat':
                                if value not in patterns:
                                    print("Pattern {} not in pattern dict".format(value))
                                else:
                                    value = patterns[value]
                            elif typ == 'change':
                                if value not in functions:
                                    print("Function {} not in function dict".format(value))
                                else:
                                    value = functions[value]
                            elif typ == 'gram':
                                if value in grams:
                                    value = grams[value]
                                else:
                                    value = FSSet.parse(value)
                            attrib_dict[typ] = value
                        if 'pos' not in attrib_dict:
                            attrib_dict['pos'] = current_pos
                        current_attribs.append(attrib_dict)
                if current_suffix:
                    # Current suffix attribs not yet added to suffixes
                    if current_suffix in self.suffixes:
                        self.suffixes[current_suffix].extend(current_attribs)
                    else:
                        self.suffixes[current_suffix] = current_attribs

    def strip_suffixes(self, word, guess=False, segment=False, incl_suf=True, verbose=False, pretty=False):
        '''
        Check to see if the word can be directly segmented into a stem and
        one or more suffixes.
        '''
        if self.suffixes:
            result = []
            stripped = iwqet.morphology.strip.sufstrip(word, self.suffixes)
            if stripped:
                for segs, gram, anal in stripped:
                    if anal:
                        # 'segs' needs to be analyzed further
                        # First separate the stem from segs and find the POS
                        stem, x, suffixes = segs.partition('+')
                        # There may be a category name for pretty output
                        suffixes, x, sufcat = suffixes.partition(' ')
                        # Now use the anal FST for that POS to transduce the stem starting
                        # from the grammatical FSSet as an initial weight
                        fst = self.morphology[anal].get_fst(generate=False, guess=guess, segment=segment)
                        anals = fst.transduce(stem, seg_units=self.seg_units, reject_same=guess,
                                              init_weight=gram)
                        if not anals:
                            continue
                        # Return each root and FS combination, as expected by language.anal_word()
                        for root, anls in anals:
                            for a in anls:
                                if pretty:
                                    a = self.morphology[anal].fs2prettylist(a)
                                    if sufcat:
                                        a.append((sufcat, suffixes))
                                        result.append([root, self.morphology[anal].fullname, a])
                                    else:
                                        if incl_suf:
                                            root = root + '+' + suffixes
                                        result.append([root, self.morphology[anal].fullname, a])
                                else:
                                    if incl_suf:
                                        root = root + '+' + suffixes
                                    result.append([root, a])
                    else:
                        if pretty:
                            gram = self.morphology[anal].fs2pretty(gram)
                        result.append([segs, gram])
            return result

    ### POS and feat conversion

    def adapt(self, spos, target, sfeats, tfeats, verbosity=0):
        """
        Adapt a target FS or FSSet according to conditions specified
        in .mrf file, returning an updated target FSSet.
        """
        if verbosity:
            print("Adapting {}, {}".format(spos, sfeats.__repr__()))
            print(" {}, {}".format(target, tfeats.__repr__()))
        if tfeats:
            if isinstance(tfeats, FeatStruct):
                tfeats = FSSet(tfeats)
        if not sfeats:
            return [[spos, tfeats]]
        # List of POS, features combinations for target
        tposfeats = self.adapt_POS(spos, target, sfeats, tfeats=tfeats)
        sfeatlist = list(sfeats)
        for index, (tp, tf) in enumerate(tposfeats):
#            if verbosity:
#                print("0  tf {} type {}".format(tf.__repr__(), type(tf)))
            tf = self.copy_feats(spos, target, sfeats, tfeats=tf,
                                 verbosity=verbosity)
#            if verbosity:
#                print("1  tf {} type {}".format(tf.__repr__(), type(tf)))
            tf = self.adapt_feats(spos, target, sfeatlist, list(tf),
                                  verbosity=verbosity)
#            if verbosity:
#                print("2  tf {} type {}".format(tf.__repr__(), type(tf)))
            tposfeats[index][1] = tf
        if verbosity:
            print("Adapted: {}".format(tposfeats.__repr__()))
        return tposfeats

    def adapt_POS(self, spos, target, sfeats, tfeats=None):
        """
        Convert the POS to another for target language.
        """
        if tfeats == None:
            tfeats = FSSet()
        elif isinstance(tfeats, FeatStruct):
            tfeats = FSSet(tfeats)
        if spos in self.morphology:
            posconv = self.morphology[spos].posconv
            if target in posconv:
                poss = []
                targfeats = []
                conversions = posconv[target]
                for condition, pos, targfeat in conversions:
                    u = sfeats.unify_FS(condition, strict=True)
                    if u and u != 'fail':
#                        if tfeats._frozen:
#                            tfeats = tfeats.unfreeze()
                        poss.append(pos)
                        targfeats.append(targfeat)
                result = []
                for p, tf in zip(poss, targfeats):
                    tf1 = tfeats.upd({'pos': p})
                    if tf:
                        tf1 = tf1.upd(tf)
                    result.append([p, tf1])
                if result:
                    return result
        return [[spos, tfeats]]

    def adapt_feats(self, spos, target, sfeatlist, tfeatlist,
                    verbosity=0):
        """
        Convert source features to target features.
        """
        if spos in self.morphology:
            featconv = self.morphology[spos].featconv
            if target in featconv:
                if verbosity:
                    print(" adapt_feats {}, {}, {}, {}".format(spos, target, sfeatlist, tfeatlist))
                if isinstance(tfeatlist, FSSet):
                    tfeatlist = list(tfeatlist)
                tfeats = tfeatlist[0] if len(tfeatlist) > 0 else FeatStruct()
                while len(tfeatlist) < len(sfeatlist):
                    tfeatlist.append(tfeats.copy())
                conversions = featconv[target]
                if verbosity:
                    print("ADAPT_FEATS tfeatlist {}".format(tfeatlist))
                if verbosity:
                    print("  conversions {}".format(conversions))
                for condition, tf in conversions:
                    for findex, sfeats in enumerate(sfeatlist):
                        u = sfeats.unify_FS(condition, strict=True)
                        if u and u != 'fail':
                            # Condition is satisfied for sfeats
                            if verbosity:
                                print(" {} UNIFIED WITH {}".format(sfeats.__repr__(),
                                                               condition.__repr__()))
                                print("  tf {}, tfeats {}".format(tf.__repr__(),
                                                              tfeats.__repr__()))
                            tfeats = tfeatlist[findex]
                            tunify = tfeats.unify_FS(tf)
                            if tunify == 'fail':
                                # Don't update tfeats with a new feature
                                # that would conflict with an existing one
#                                print(" Skipping {}->{}".format(condition.__repr__(), tf.__repr__()))
                                continue
#                            print("  UPDATING {}".format(tfeats.__repr__()))
                            if not tf:
                                # No change to source feature
                                tfeats = tfeats.upd(condition)
                            else:
                                tfeats = tfeats.upd(tf)
                            tfeatlist[findex] = tfeats
        return FSSet(tfeatlist)

    def copy_feats(self, spos, target, sfeats, tfeats=None,
                   verbosity=0):
        """
        Copy source features to target features.
        """
        if verbosity:
            print(" copy_feats: {}, {}, {}, {}".format(spos, target, sfeats, tfeats))
        if not tfeats:
            tfeats = FSSet()
        if spos in self.morphology:
            featcopy = self.morphology[spos].featcopy
            if target in featcopy:
                copyfeats = featcopy[target]
                copydct = dict([(f, f) for f in copyfeats])
#                print(" COPY FEATS dct {}".format(copydct))
                tfeats = sfeats.agree(tfeats, copydct, force=False)
        return tfeats

    def anal_word(self, word, guess=True, only_guess=False, segment=False,
                  root=True, stem=True, citation=True, gram=True,
                  # Whether to return a pretty list of feature values
                  # (doesn't work within Mbojereha yet)
                  pretty=False,
                  # Whether to return empty analyses / all analyses
                  unanal=False, get_all=True,
                  # Whether to include stripped suffixes (e.g., abrir+lo)
                  incl_suf = False,
                  to_dict=False, preproc=True, postproc=False,
                  # Whether to cache new entries and to check cache
                  cache=True, check_cache=True,
                  no_anal=None, string=False, print_out=False, only_anal=False,
                  rank=True, report_freq=True, nbest=100,
                  # Whether to normalize orthography before analysis
                  clean=True,
                  verbosity=0):
        '''
        Morphologically analyze a single word, trying all existing POSs,
        both lexical and guesser FSTs.
        '''
        # First make sure the analysis FSTs are loaded for this language
        if self.use in (GENERATION, TARGET):
            print("Analyzer for {} not loaded".format(self))
            return
        # Before anything else, check to see if the word is in the list of words that
        # have failed to be analyzed
        if no_anal != None and word in no_anal:
            return None
        # Next clean up using character conversion dict
        if clean:
            # This may already have taken place in Sentence.
            for d, c in self.clean.items():
                if d in word:
                    word = word.replace(d, c)
        analyses = []
        to_cache = [] if cache else None
        if self.romanize:
            word = self.romanize(word)
        unal_word = self.morphology.is_unal_word(word)
        # unal_word is a form, POS pair
        if unal_word:
            # Don't cache these
            cache = False
            if only_anal:
                return []
            a = self.simp_anal(unal_word, postproc=postproc, segment=segment)
            analyses.append(a)
        # See if the word is cached (before preprocessing/romanization)
        if check_cache:
            cached = self.get_cached_anal(word)
            if cached:
                if verbosity:
                    print("Found {} in cached analyses".format(word))
                if not pretty:
                    analyses = cached
                else:
                    analyses = self.prettify_analyses(cached)
                return analyses
        form = word
        # Try stripping off suffixes
        suff_anal = self.strip_suffixes(form, incl_suf=incl_suf, pretty=pretty)
        if suff_anal:
#            print("Suff anal {}".format(suff_anal))
            analyses.extend(suff_anal)
            if cache and not pretty:
                to_cache.extend(suff_anal)

        if not analyses or get_all:
            # Nothing worked so far or getting everything...
            if not only_guess:
                for pos, POS in self.morphology.items():
                    #... or already analyzed within a particular POS
                    preanal = POS.get_analyzed(form, sep_anals=True,
                                               pretty=pretty)
                    if preanal:
                        analyses.extend(preanal)
                        if cache and not pretty:
                            to_cache.extend(preanal)
                if not analyses or get_all:
                    if not only_guess:
                        # We have to really analyze it; first try lexical FSTs for each POS
                        for pos, POS in self.morphology.items():
                            analysis = POS.analyze(form, segment=segment,
                                                   preproc=preproc,
                                                   to_dict=to_dict,
                                                   sep_anals=False,
                                                   pretty=pretty)
                            if analysis:
                                analyses.extend(analysis)
                                if cache and not pretty:
                                    to_cache.extend(analysis)
                    # If nothing has been found, try guesser FSTs for each POS
                    if not analyses and guess:
                        # Accumulate results from all guessers
                        for pos, POS in self.morphology.items():
                            analysis = POS.analyze(form, guess=True,
                                                   preproc=preproc,
                                                   segment=segment,
                                                   to_dict=to_dict,
                                                   sep_anals=True,
                                                   pretty=pretty)
                            if analysis:
                                analyses.extend(analysis)
                                if cache and not pretty:
                                    to_cache.extend(analysis)

        if cache and not pretty:
            # Cache new analyses
            self.add_new_anal(word, to_cache)

        if not analyses:
            return [{'root': word, 'features': ''}]

#        print("Analyses: {}".format(analyses))

        # Sort the analyses by feature-value ranking
        self.morphology.sort_analyses(analyses)

        return self.dictify_analyses(analyses)

    def simp_anal(self, analysis, postproc=False, segment=False):
        '''Process analysis for unanalyzed cases.'''
        if segment:
            return analysis[0], analysis[1], 100000
        elif postproc:
            # Convert the word to Geez.
            analysis = (analysis[0], self.postproc(analysis[1]))
#        if segment:
#            return analysis
        pos, form = analysis
        analysis = [form, {'pos': pos}]
        # 100000 makes it likely these will appear first in ranked analyses
        return analysis #pos, form, None, None, None, 100000

    def dictify_analyses(self, anals):
        """Convert a list of (root, FS) analyses to a list of dicts,
        and convert roots to _ form."""
        dicts = []
        for root, anal in anals:
            pos = anal.get('pos', '')
            dicts.append({'root': Language.make_root(root, pos), 'features': anal})
        return dicts

    def disambiguate_POS(self, word, context, index, n=50, verbosity=0):
        """
        Use stored POS collocations to prefer one tag over another,
        given lists of tags preceding and following word, output of tagger.
        """
#        print("Disambiguating {} in context {}".format(word, context))
        entry = self.POSambig.get(word)
        if not entry:
            return
        precontext = context[:index]
        if len(precontext) == 1:
            precontext = [('EOS', 'X')] + precontext
        elif len(precontext) == 0:
            precontext = [(".", "pnc"), ('EOS', 'X')]
        postcontext = context[index+1:]
        if len(postcontext) == 1:
            postcontext.append(('EOS', 'X'))
        elif len(postcontext) == 0:
            postcontext = [('EOS', 'X'), ('EOS', 'X')]
        scores = {}
        for tag, anals in entry.items():
            score = self.disambig_score(precontext, postcontext, tag, n=n)
            if not score:
                if verbosity:
                    print("No collocs for tag {}!".format(tag))
                return
            if verbosity:
                print(" Score for {}: {}".format(tag, score))
            scores[tag] = (Language.scale_disambig_score(score), anals)
        if verbosity:
            print("Scores: {}".format(scores))
        # Select highest
        highest = -1
        highestfeats = None
        for tag, (score, features) in scores.items():
            if score > highest:
                highest = score
                highestfeats = features
        # return a copy of the winning list of roots and features
        highestcopy = []
        for dct in highestfeats:
            # copy each dict
            dctcopy = {}
            dctcopy['root'] = dct['root']
            # copy each FSSet
            features = dct['features']
            if isinstance(features, str):
#                print("Features for {} is string {}".format(word, features))
                dctcopy['features'] = features
            else:
                dctcopy['features'] = dct['features'].copyFSS()
            highestcopy.append(dctcopy)
        return highestcopy

    def disambiguate_cache(self, word, tag):
        """
        Try disambiguating using ordered cached analyses and tag from tagger.
        If the tag agrees with the POS tag for the first cached analysis,
        accept it (only).
        """
        cached = self.get_cached_anal(word)
        if not cached:
            return
#        print("{}: checking tag {} and cached analyses {}".format(word, tag, cached))
        # most frequent analysis
        cached0 = cached[0]
        # does POS agree?
        cachePOS = ''
        if 'pos' in cached0:
            cachePOS = cached0['pos']
        elif 'features' in cached0:
            cachePOS = cached0['features'].get('pos', '')
        if cachePOS == tag:
#            print("{}: cached pref {} agrees with tag".format(word, tag))
            return cached0
        return

    @staticmethod
    def scale_disambig_score(values, n=50):
        return sum(values)

    def disambig_score(self, precontext, postcontext, tag, n=50):
        """
        Given a word and its preceding and following context tags
        (lists of word, tag pairs) and pre- and post-collocations for a
        given POS tag, calculate a score: index of perfect matches and
        number of single (one tag) matches.
        """
        collocs = self.collocs.get(tag)
        if not collocs:
            return
        precollocs, postcollocs = collocs
        perfpre = 0
        perfpost = 0
        partpre = 0
        partpost = 0
        precont = [c[1] for c in precontext[-2:]]
        postcont = [c[1] for c in postcontext[:2]]
        for index, precol in enumerate(precollocs):
            i = n - index + 1
            if not perfpre and precont == precol:
                perfpre = i
            elif precont[1] == precol[1]:
                partpre += 1
        for index, postcol in enumerate(postcollocs):
            i = n - index + 1
            if not perfpost and postcont == postcol:
                perfpost = i
            elif postcont[1] == postcol[1]:
                partpost += 1
        return perfpre, partpre, perfpost, partpost

    @staticmethod
    def make_root(root, pos):
        """Add the _ expected for roots."""
        if not root.endswith("_{}".format(pos)):
#        if '_' not in root:
            if pos == 'nadj' or pos == 'adj' or pos.startswith('nm'):
                pos = 'n'
            root = root + '_' + pos
        return root

    def prettify_analyses(self, anals):
        a = []
        for root, fs in anals:
            pos = fs.get('pos')
            posmorph = self.morphology.get(pos)
            a.append((root, posmorph.fullname, posmorph.fs2prettylist(fs)))
        return a

    def get_gen_fvs(self):
        gf = []
        for f, m in self.morphology.items():
            gf.append(((f, m.fullname), m.get_gen_fvs()))
        return gf

    def form2fvs(self, selpos, form):
        """
        Convert a dict of feature, value pairs from web form to L3Morpho
        feat val dicts, one for the form, one for generation.
        Record only those features belonging to the selected POS. Features
        are those keys containing ':'.
        """
        fvs = {}
        longfvs = {}
        for f, v in form.items():
            if ':' not in f:
                continue
            fsplit = f.split(':')
            pos = fsplit[0]
            if pos == selpos:
                posmorph = self.morphology[pos]
                f1long = fsplit[1]
                f1 = posmorph.exrevab(f1long)
                f2 = None
                if len(fsplit[1:]) == 2:
                    f2long = fsplit[2]
                    f2 = posmorph.exrevab(f2long)
                if f2:
                    if f1 not in fvs:
                        fvs[f1] = {}
                        longfvs[f1long] = {}
                    fvs[f1][f2] = True
                    longfvs[f1long][f2long] = 'on'
                else:
                    fvs[f1] = posmorph.exrevab(v)
                    if v is True:
                        longfvs[f1long] = 'on'
                    else:
                        longfvs[f1long] = v
        return fvs, longfvs

    ### End of morphology stuff

    def to_dict(self):
        """
        Convert the language to a dictionary to be serialized as a yaml file.
        This is old and needs to be updated.
        """
        d = {}
        d['name'] = self.name
        d['abbrev'] = self.abbrev
        if self.groups:
            groups = {}
            for head, v in self.groups.items():
                groups[head] = [g.to_dict() for g in v]
            d['groups'] = groups
        return d

    def write(self, directory, filename=''):
        """Serialize the language."""
        filename = filename or self.abbrev + '.lg'
        path = os.path.join(directory, filename)
        with open(path, 'w', encoding='utf8') as file:
            yaml.dump(self.to_dict(), file)

    def read_group(self, gfile, gname=None, target=None,
                   reverse=False,
                   source_groups=None, target_groups=None, target_abbrev=None,
                   groupcats=None, posindex=0, verbosity=0):
        """
        Read in a single group type from a file with path gfile and name gname.
        """
        with open(gfile, encoding='utf8') as file:
            gname = gname or gfile.rpartition('/')[-1].split('.')[0]
            groupdefaults = []
            if verbosity:
                print("  Reading groups of type {}".format(gname))
            # Groups separated by GROUP_SEP string
            groups = file.read().split(GROUP_SEP)
            transadd = ''
            sourceadd = ''
            # Preamble precedes first instance of GROUP_SEP
            preamble = groups[0]
            # Handle preamble ...
            for line in preamble.split("\n"):
                line = line.strip()
                if not line or line[0] == '#':
                    continue
                if line[0] == '+':
                    tp, x, addition = line.partition(' ')[2].partition(' ')
                    if line[1] == 't':
                        transadd = tp, addition
                        groupdefaults.append(transadd)
                    else:
                        sourceadd = addition
                        groupdefaults.append(sourceadd)
            if groupdefaults:
                self.group_defaults[gname] = groupdefaults
            for group_spec in groups[1:]:
                group_trans = group_spec.split('\n')
                n = 0
                group_line = group_trans[n].strip()
                while len(group_line) == 0 or group_line[0] == '#':
                    # Skip comment lines
                    n += 1
                    group_line = group_trans[n].strip()
                # A string starting with tokens and with other attributes separated by ;
                if ALT_SEP in group_line:
                    group_line = group_line.split(ALT_SEP)
                    source_group = group_line
                else:
                    source_group = [group_line]
                    # Not sure whether head should be used to speed up reading
                    # group from string?
                source_groups.extend(source_group)
                translations = []
                trans_strings = []
                n += 1
                if target:
                    for t in group_trans[n:]:
                        # Skip comment lines
                        if len(t) > 0 and t[0] == '#':
                            continue
                        t = t.partition(TRANS_START)[2].strip()
                        if t:
                            t = t.strip()
                            trans_strings.append(t)
                            # Or use the Group method add_trans_default() for this.
                            tlang, x, tgroup = t.strip().partition(' ')
                            if transadd:
                                tp, ad = transadd
                                if tp not in tgroup:
                                    tgroup += " " + ad
                            if tlang == target_abbrev:
                                translations.append(tgroup)

                    target_groups.extend(translations)

                # Creates the group and any target groups specified and adds
                # them to the appropriate groups
                # As of 2020.9.8, there may be multiple source groups
                for sg in source_group:
                    g, t_agr, align, t_count = \
                    Group.from_string(sg, self, translations,
                                      target=target, trans=False,
                                      tstrings=trans_strings,
                                      cat=gname, posindex=posindex)
                    if reverse:
                        for tgroup, tfeatures in g.trans:
                            tgroup.reverse_trans(g, tfeatures)

    def read_groups(self, posnames=None, target=None,
                    reverse=False, verbosity=0):
        """
        Read in groups from .grp files. If target is not None (must be a
        language), read in translation groups and cross-lingual features as well.
        """
        target_abbrev = target.abbrev if target else None
        source_groups = []
        target_groups = []
        print("Reading lexical groups for {}".format(self))
        groupfiles = self.get_grouplist_files(posnames)
        for name, gfile in self.get_group_files(posnames):
            posindex = firstindex(lambda x: name in x, self.groupcats) if self.groupcats else 0
            self.read_group(gfile, gname=name, target=target, source_groups=source_groups,
                            target_groups=target_groups, target_abbrev=target_abbrev,
                            reverse=reverse,
                            verbosity=verbosity, posindex=posindex)

        # Sort groups for each key by priority
        for groups in self.groups:
            for key, groups1 in groups.items():
                if len(groups1) > 1:
                    groups1.sort(key=lambda g: g.priority(), reverse=True)

        # Add unambiguous groups to related source ambiguous groups
        self.update_sambig_groups()

    def write_group_defaults(self, cat, stream):
        """Write the group defaults for category cat to stream."""
        defaults = self.group_defaults.get(cat)
        if defaults:
            for default in defaults:
                # Assumes translation default
                tp, addition = default
                print("+t {} {}".format(tp, addition), file=stream)

    def update_groups(self, write=False):
        """Use transcounts file to order translations of all groups.
        If write is True, rewrite the updated groups in the appropriate file."""
        for pos, cats in enumerate(self.groupcats):
            for cat in cats:
                self.update_group(pos=pos, cat=cat, write=write)

    def update_group(self, groups=None, pos=0, cat='v1', write=False):
        """Use transcounts file to order translations of groups in cat.
        If write is True, rewrite the updated groups in the appropriate file."""
        groups = groups or Group.get_cat_groups(self, cat, pos)
        ordered = False
        for group in groups:
            ordered = group.order_trans() or ordered
        if write and ordered:
            Group.rewrite_groups(self, cat, groups)

    def read_ms(self, target=None, verbosity=0):
        """Read in MorphoSyns for target from a .ms file. If target is not None (must be a language), read in translation groups
        and cross-lingual features as well."""
        path = self.get_ms_file(target.abbrev)
        try:
            with open(path, encoding='utf8') as f:
                print("Reading morphosyntactic transformations for {}".format(target))
                lines = f.read().split('\n')[::-1]
                # the order of MorphoSyns matters
                while lines:
                    # Strip comments
                    line = lines.pop().split('#')[0].strip()
                    # Ignore empty lines
                    if not line: continue
                    name, x, tokens = line.partition(MS_NAME_SEP)
                    morphosyn = MorphoSyn(self, name=name.strip(), tokens=tokens.strip())
                    self.ms.append(morphosyn)
                    # If there are optional Morphosyns associated with this Morphosyn add them too.
                    if morphosyn.optional_ms:
                        self.ms.extend(morphosyn.optional_ms)
        except IOError:
            print('No such MS file as {}'.format(path))

    @staticmethod
    def read_mwe(abbrev='spa', name='1', verbosity=0):
        path = Language.get_mwe_file(abbrev, name=name)
        mwes = []
#        print("Reading MWE")
        try:
            with open(path, encoding='utf8') as f:
                for line in f:
                    line = line.strip()
                    if line:
                        line = line.split(',')
                        mwes.append((line[0].split(Entry.mwe_sep), line[1].strip()))
            return mwes
        except IOError:
            print("No such MWE file as {}".format(path))

    def read_joins(self, target=None, verbosity=0):
        """Read in Join patterns for target from a .jn file."""
        path = self.get_join_file(target.abbrev)
        grouping = []
        try:
            with open(path, encoding='utf8') as f:
                print("Reading patterns for joining segments for {}".format(target))
                lines = f.read().split('\n')[::-1]
                # the order of Joins matters
                while lines:
                    # Strip comments
                    line = lines.pop().split('#')[0].strip()
                    # Ignore empty lines
                    if not line: continue
                    grp = Language.joingrp.match(line)
                    if grp:
                        if grouping:
                            self.join_groupings.append(grouping)
                            grouping = []
                        continue
                    name, x, tokens = line.partition(JOIN_NAME_SEP)
                    join = Join(self, target, name=name.strip(), tokens=tokens.strip())
                    grouping.append(join)
            # add last grouping
            self.join_groupings.append(grouping)
        except IOError:
            print('No such Join file as {}'.format(path))

    @staticmethod
    def string2value(string):
        if string.isdigit():
            return int(string)
        elif string == "False":
            return False
        elif string == 'True':
            return True
        elif string == 'None':
            return None
        else:
            return string

    @staticmethod
    def from_dict(d, reverse=True, use=ANALYSIS, directory=None):
        """Convert a dict (loaded from a file) to a Language object."""
        exttag = d.get('exttag')
        joins = d.get('join')
        namejoin = d.get('namejoin', '').split(',')
        groupcats = d.get('groups') # d.get('groupcats')
        mwe = d.get('mwe')
        abbrev = d.get('abbrev')
        collocs = d.get('collocs')
        disambig_feats = d.get('disambfeats')
        disambig_agree = d.get('disambagree')
        disambig_penalties = d.get('disambpen')
        geez = d.get('geez')
        if disambig_feats:
            disambig_feats = disambig_feats.split(',')
            disambig_feats = [tuple(df.split(':')) if ':' in df else df for df in disambig_feats]
        if disambig_agree:
            disambig_agree = disambig_agree.split(';')
            disambig_agree = [da.split('==') for da in disambig_agree]
            disambig_agree = [([tuple(da.split(':')) if ':' in da else da for da in dis_agree[0].split(',')], Language.string2value(dis_agree[1]))\
                               for dis_agree in disambig_agree]
        if disambig_penalties:
#            print("disambpen {}".format(disambig_penalties))
            disambig_penalties = [dp.split('==') for dp in disambig_penalties.split(';')]
            disambig_penalties = dict([(tuple(dp0.split(':')) if ':' in dp0 else dp0, float(dp1)) for dp0, dp1 in disambig_penalties])
        if collocs:
            collocs = collocs.split(',')
        if groupcats:
            groupcats = [g.split(',') for g in groupcats.split(';')]
        conversion = None
        if exttag:
            # External tagger, so also look for conversion dictionaries for tags
            feat_conv = d.get('morphology')
            # Convert this to a dict with (word, tag) keys and lemma, FSSet values
            if feat_conv:
                new_feat_conv = {}
                for key, (lemma, feats) in feat_conv.items():
                    wrd_tag = key.split('|')
                    tag = wrd_tag[0]
                    wrd = wrd_tag[1] if len(wrd_tag) == 2 else ''
                    new_feat_conv[(wrd, tag)] = (lemma, feats)
                conversion = (d.get('pos'), new_feat_conv)
        if mwe:
            mwe = Language.read_mwe(abbrev=abbrev, name=mwe)
            mwe = Language.treeify(mwe)
        elif joins:
            joins = [(x.split('~'), y) for x, y in joins]
            mwe = Language.treeify(joins)
        l = Language(d.get('name'), abbrev, use=use, directory=directory,
                     exttag=exttag, conversion=conversion, postags=d.get('postags'),
                     mwe=mwe, eos=d.get('eos', EOS), collocs=collocs,
                     disambig_feats=disambig_feats,
                     disambig_agree=disambig_agree,
                     disambig_penalties=disambig_penalties,
#                     lemmas=d.get('lemmas'),
                     namejoin=namejoin, groupcats=groupcats,
                     geez=geez)
        translations = d.get('translations')
        if translations:
            for s, t in translations.items():
                l.translations[s] = t
        # Create classes and patterns
        if 'classes' in d:
            for k, v in d.get('classes'):
                l.classes[k] = v.split()
        if 'patterns' in d:
            for k, v in d.get('patterns'):
                tokens = v.split()
                l.patterns[k] = tokens
                l.pattern_list.append((k, tokens))
        return l

    @staticmethod
    def read(path, use=ANALYSIS, directory=None, verbosity=0):
        """
        Create a Language from the contents of a file, a dict that must
        be then converted to a Language.
        2017.4.18: Stopped using YAML.
        2019: Probably should go back to YAML because it pretty much is already.
        """
        dct = {}
        key = ''
        subdct = {}
        ls = []
        with open(path, encoding='utf8') as file:
            lines = file.read().split('\n')[::-1]
            while lines:
                line = lines.pop().split('#')[0].strip() # strip comments
                if not line: continue                    # ignore blank lines
                if verbosity:
                    print("Key {}, subdict {}, line {}".format(key, subdct, line))
                splitline = line.split()
                if '::' in line:
                    # key and value for subdict
                    # We need rpartition rather than split to handle the case :::pct
                    subkey, xx, value = line.rpartition('::')
                    subkey = subkey.strip()
                    value = value.strip()
                    if '|' in value:
                        value = value.split('|')
                        value = [v for v in value if v]
                    subdct[subkey] = value
                    continue
                if splitline[0].endswith(':'):
                    # the name of a new dict key
                    if len(splitline) > 1:
                        # if there's a subdct, incorporate it
                        if subdct and key:
                            dct[key] = subdct
                            key = ''
                            subdct = {}
                        # if there's a sublist, incorporate it
                        elif ls and key:
                            dct[key] = ls
                            key = ''
                            ls = []
                        # the value is in this line
                        key = splitline[0][:-1]
                        value = splitline[1]
                        dct[key] = value
                        if verbosity:
                            print("  Key {}, value {}".format(key, value))
                        key = ''
                    else:
                        # the name of subdct
                        # First add the last one
                        if subdct and key:
                            if verbosity:
                                print("  Adding last subdict {} to {}".format(subdct, key))
                            dct[key] = subdct
                            subdct = {}
                        elif ls and key:
                            if verbosity:
                                print("  Adding last sublist {} to {}".format(sublist, key))
                            dct[key] = ls
                            ls = []
                        key = splitline[0][:-1]
                    continue
                if line[0] == '-':
                    # Sublist to add to list
                    sublist = line.split('-')[1].strip()
                    sublist = sublist.split(',')
                    if verbosity:
                        print("  Sublist item: {}".format(sublist))
                    ls.append([x.strip() for x in sublist])
                    continue
                if line[0] == ' ':
                    print("{} begins with space".format(line))
                print("Something wrong with line {}".format(line))

        # Add left-over subdicts or sublist to current key
        if subdct and key:
            if verbosity:
                print("  Adding subdict {} to {}".format(subdct, key))
            dct[key] = subdct
        elif ls and key:
            if verbosity:
                print("  Adding sublist {} to {}".format(sublist, key))
            dct[key] = ls
        return Language.from_dict(dct, use=use, directory=directory)

    @staticmethod
    def load_trans(source, target, bidir=False):
        """
        Load a source and a target language, given as abbreviations.
        Read in groups for source language, including target language translations
        at the end.
        If bidir is True, load analysis and generations FST for both languages
        and groups in both directions.
        If the languages are already loaded, don't load them.
        """
        srclang = Language.languages.get(source)
        targlang = Language.languages.get(target)
        src_loaded = False
        targ_loaded = False
        srcuse = BIDIR if bidir else SOURCE
        targuse = BIDIR if bidir else TARGET
        if srclang:
#            print("Srclang use: {}".format(srclang.use))
            if srclang.use in (SOURCE, BIDIR):
                print("Source language {} already loaded".format(srclang))
            else:
                print("Adding morphology for {}".format(srclang))
                srclang.set_anal_cached()
                srclang.load_morphosyntax(targlang)
                srclang.load_morpho(analyze=True, generate=False, guess=False)
                srclang.use = BIDIR
            if bidir:
                if srclang.use in (TARGET, BIDIR):
                    print("Target language {} already loaded".format(srclang))
                else:
                    # Source language is loaded as source but needs to have
                    # generation FSTs as well.
                    print("Adding morphology for {}".format(srclang))
                    srclang.load_morpho(analyze=False, generate=True, guess=False)
                    srclang.use = BIDIR
            src_loaded = True
        if targlang:
#            print("Targlang use: {}".format(targlang.use))
            if targlang.use in (TARGET, BIDIR):
                print("Target language {} already loaded".format(targlang))
            else:
                print("Adding morphology for {}".format(targlang))
                targlang.load_morpho(analyze=False, generate=True, guess=False)
                targlang.use = BIDIR
            if bidir:
                if targlang.use in (SOURCE, BIDIR):
                    print("Target language {} already loaded".format(targlang))
                else:
                    # Target is loaded as target, needs source morphosyntax
                    # and FSTs as well.
#                    print("Leyendo ", end='')
                    targlang.load_morphosyntax(srclang)
#                    targlang.read_groups(target=srclang)
                    targlang.load_morpho(analyze=True, generate=False, guess=False)
                    targlang.use = BIDIR
            targ_loaded = True
        if src_loaded and targ_loaded:
            return srclang, targlang
        try:
            if not srclang:
                srcpath = os.path.join(Language.get_language_dir(source), source + '.lg')
                srclang = Language.read(srcpath, use=srcuse)
                print("Source language {} loaded".format(srclang))
            if not targlang:
                targpath = os.path.join(Language.get_language_dir(target), target + '.lg')
                targlang = Language.read(targpath, use=targuse)
                print("Target language {} loaded".format(targlang))
        except IOError:
            print("One of these languages doesn't exist.")
            return
        # Load groups for source language now
        if not src_loaded:
            srclang.load_morphosyntax(targlang, reverse=bidir)
        if bidir and not targ_loaded:
            targlang.load_morphosyntax(srclang)
        # if not src_loaded:
        #     srclang.read_ms(target=targlang)
        #     srclang.read_joins(target=targlang)
        #     srclang.read_transcounts(target)
        #     srclang.read_groups(posnames=groups, target=targlang)
        return srclang, targlang

    def load_morphosyntax(self, target, reverse=False):
        """
        Load Morphosyns, Joins, translation counts, and groups for a
        source language.
        """
        self.read_ms(target=target)
        self.read_joins(target=target)
        self.read_transcounts(target.abbrev)
        self.read_groups(target=target, reverse=reverse)

    @staticmethod
    def load_lang(lang, groups=None):
        """Load a language, given as an abbreviation, for parsing only.
        Read in groups for language. If the language is already loaded, don't load it."""
        srclang = Language.languages.get(lang)
        loaded = False
        if srclang and srclang.use == ANALYSIS:
            loaded = True
        else:
            try:
                srcpath = os.path.join(Language.get_language_dir(lang), lang + '.lg')
                srclang = Language.read(srcpath, use=ANALYSIS)
                print("Language {} loaded".format(srclang))
            except IOError:
                print("Language doesn't exist.")
                return
        # Load groups for source language now
        if not loaded:
            srclang.read_groups(posnames=groups)
        return srclang

    @staticmethod
    def load(*abbrevs):
        """Load languages, given as abbreviations."""
        languages = []
        for abbrev in abbrevs:
            if abbrev in Language.languages:
                language = Language.languages[abbrev]
                languages.append(language)
            else:
                path = os.path.join(Language.get_language_dir(abbrev), abbrev + '.lg')
                try:
                    language = Language.read(path)
                    languages.append(language)
                    print("Loaded language {}".format(language))
                except IOError:
                    print("That language doesn't seem to exist.")
                    return
        return languages

    def translate_special(self, form):
        """Translate a special form, for example, a numeral. Default is to just return the form."""
#        print("Translating {}".format(form))
        if not form:
            return form
        form1 = form[1:]
        # See if form's translation is in the translation dict
        if form1 in self.translations:
            return '%' + self.translations[form1]
        return form

    @staticmethod
    def get_grouptoken(string):
        if '_' in string:
            return string.rpartition('_')[0]
        else:
            return string

    def add_group(self, group, cat=None, posindex=0):
        """Add group to dict, indexed by head."""
        head = group.head
        self.groupnames[group.name] = group
        token = Language.get_grouptoken(head)
        if token in self.group_keys:
            self.group_keys[token].add(head)
        else:
            self.group_keys[token] = {head}
        group.language = self
        group.set_pos()
        groups = self.groups[posindex]
        if head in groups:
            groups[head].append(group)
        else:
            groups[head] = [group]
        # Create entry for source ambiguous groups
        if group.is_sambig():
            self.sambig_groups[group] = []
        self.changed = True

    def update_sambig_groups(self):
        """Once groups have been created, add related unambiguous groups for
        each source ambiguous group, for example ir_v and ser_v for ir|ser_v."""
        for sambig, unambig in self.sambig_groups.items():
            root = sambig.root
            pos = sambig.pos
            posindex = sambig.posindex
            if root and pos:
                roots = root.split('|')
                heads = [r + "_" + pos for r in roots]
                for head in heads:
                    groups = self.groups[posindex].get(head)
                    if groups:
                        match = firsttrue(lambda g: sambig.match_non_head(g), groups)
                        if match:
                            unambig.append(match)

    ### Generation of word forms

    def mult_generate(self, root, posfeats, guess=False, roman=True,
                      cache=False, verbosity=0):
        """
        When a single root has multiple POS/feature combinations to
        generate, use this.
        """
        if verbosity:
            print("Mult gen {} {}".format(root, posfeats))
        outstrings = []
        outfeats = []
        for pos, feats in posfeats:
            strings1, feats1 = \
              self.generate(root, feats, pos, guess=guess, roman=roman,
                            cache=cache, verbosity=verbosity)
            if feats1:
                # only record the output if generate() succeeds
                outstrings.extend(strings1)
                outfeats.extend(feats1)
#        print("Generated {}".format(outstrings))
        return outstrings, outfeats

    def generate(self, root, features, pos=None, guess=False, roman=True,
                 cache=False, verbosity=0):
        """2017.5.19:
        features may now be an FSSet; should probably be the only option.
        """
        # In Amharic features may override the POS provided
        # (needed for verbal nouns), but this doesn't apply
        if verbosity:
            print("Generating {}:{} with POS {}".format(root, features.__repr__(), pos))
        if not pos:
            # generate() shouldn't have been called in this case!
            print("Warning: no POS for generation of {}:{}".format(root, features.__repr__()))
        is_not_roman = not roman
        morf = self.morphology
        output = []
        if isinstance(features, (bool, str)):
            # features may be True and (for some reason) the string 'fail'
            return [root], []
        elif pos:
            if pos not in morf:
                print("POS {} not in morphology {}".format(pos, morf))
                return [root], []
            posmorph = morf[pos]
            if verbosity:
                print(" Generating with {}".format(posmorph))
            output = posmorph.gen(root, update_feats=features,
                                  del_feats=True,
                                  guess=guess, cache=cache)
        else:
            for posmorph in list(morf.values()):
                if verbosity:
                    print(" Generating with {}".format(posmorph))
                output.extend(posmorph.gen(root, update_feats=features,
                                           del_feats=True, guess=guess))
        if output:
            # separate output strings from features
            output_strings = [o[0] for o in output]
            output_feats = [o[1] for o in output]
            # if there is a postprocessing dict, apply it
            if self.postproc:
                self.char_postproc_list(output_strings)
            if self.orthographize:
                for oi, outp in enumerate(output_strings):
                    output_strings[oi] = self.orthographize(outp)
#            if self.postsyll:
#                # There is a syllabic postprocessing dict, apply it
#                for oi, outp in enumerate(output_strings):
#                    output_strings[oi] = self.syll_postproc(outp)
#            print("generate({}) => {}, {}".format(root, output_strings, output_feats))
            return output_strings, output_feats
        else:
#            print("   The root/feature combination {}:{} can't be generated for POS {}!".format(root, features.__repr__(), pos))
            # Add * to mark this is a uninflected.
            root = self.char_postproc(root)
            return ['*' + root], []

    def gen_multroots(self, roots, features, pos=None, guess=False, roman=True, cache=True, verbosity=0):
        """For multiple roots and the same features, return the list of possible outputs."""
        features = FeatStruct(features)
        output = []
        for root in roots:
            outputs.extend(self.generate(root, features, pos=pos, guess=guess, roman=roman, cache=cache, verbosity=verbosity))
        return output

    def char_postproc(self, form):
        """Replace characters in form using the postproc dict."""
        for d, c in self.postproc.items():
            if d in form:
                form = form.replace(d, c)
        return form

    def char_postproc_list(self, forms):
        """Replace forms in list of strings forms using the postproc dict."""
        for i, form in enumerate(forms):
            for d, c in self.postproc.items():
                if d in form:
                    forms[i] = form.replace(d, c)

    def punc_postproc(self, punc):
        """Convert punctuation to another script if possible."""
        if self.postpunc:
            return self.postpunc.get(punc, punc)
        return punc

    def syll_postproc(self, form, replace_gem=True):
        """Convert romanized form to a representation in a syllabary. Only currently works for Ethiopian Semitic."""
        dct = self.postsyll
        vowels = self.vowels
        # First delete gemination characters if required
        if replace_gem:
            form = form.replace(self.gem_char, '')
        # Segment
        res = ''
        n = 0
        nochange = False
        while n < len(form):
            char = form[n]
            if n < len(form) - 1:
                next_char = form[n + 1]
                if next_char in vowels:
                    # Doesn't handle long vowels
                    trans = dct.get(form[n : n + 2], char + next_char)
                    n += 1
                elif next_char == 'W' or next_char == 'Y' or char == '^':
                    # Consonant represented by 2 roman characters; this needs to be more general obviously
                    if n < len(form) - 2 and form[n + 2] in vowels:
                        # followed by vowel
                        trans = dct.get(form[n : n + 3], char + next_char + form[n + 2])
                        n += 1
                        # followed by consonant
                    else:
                        trans = dct.get(form[n : n + 2], char + next_char)
                    n += 1
                else:
                    trans = dct.get(char, char)
            else:
                trans = dct.get(char, char)
            res += trans
            n += 1
        return res

class LanguageError(Exception):
    '''Class for errors encountered when attempting to update the language.'''

    def __init__(self, value):
        self.value = value

    def __str__(self):
        return repr(self.value)
