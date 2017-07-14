########################################################################
#
#   This file is part of the Mainumby project within the PLoGS meta-project
#
#   Copyleft 2015, 2016, 2017;  HLTDI, PLoGS <gasser@indiana.edu>
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
#   --------------------------------------------------------------------
#   Author: Michael Gasser <gasser@indiana.edu>
#
#   Morphological processing.
#
# 2017.5.19
# -- Made gen() work with update_feats that's an FSSet rather than just a FeatStruct

from .fst import *
import sys

## Default punctuation characters
# Single quote eliminated 2013.08.12
PUNCTUATION = r'[“‘”’–—…¿¡•:;/\\,<>?.!%$()[\]{}|#@&*\-_+=\"\`^~]'
## Default alphabetic characters
CHARACTERS = r'[a-zA-Z]'

class Morphology(dict):
    """A dict of POSMorphology dicts, one for each POS class that has bound morphology."""

    version = 1.3
    complex = 0
    simple = 1

    def __init__(self, pos_morphs=[],
                 punctuation=PUNCTUATION, characters=CHARACTERS):
        dict.__init__(self)
#        if fsh:
#            self.set_fsh(*fsh)
#        else:
#            self.fsh = None
        self.pos = []
        for pos_morph in pos_morphs:
            label = pos_morph
            posmorph = POSMorphology(pos_morph)
            self[label] = posmorph
            posmorph.morphology = self
            self.pos.append(label)
        # Function that simplifies orthography
        self.simplify = None
        # Function that converts phonological to orthographic representation
        self.orthographize = None
        # Function that returns trivially analyzable forms
        self.triv_anal = None
        # Function that converts (POS, root, citation, FS) to a string
        self.anal2string = None
        # Pair of lists of unanalyzable words: (complex, simple)
        self.words = [[], []]
        self.words_phon = [{}, {}]
        self.seg_units = []
        self.language = None
        # Dictionary of preanalyzed words (varying POS)
        self.analyzed = {}
        self.analyzed_phon = {}
        # FST for making forms phonetic
        self.phon_fst = None
        self.directory = ''
        self.punctuation = punctuation
        self.characters = characters
        # Make punctuation regular expression objects and substitution string
        self.init_punc(characters, punctuation)

    def get_lex_dir(self):
        return os.path.join(self.directory, 'lex')

    def get_fst_dir(self):
        return os.path.join(self.directory, 'fst')

    def get_cache_dir(self):
        """File with cached analyses."""
        return os.path.join(self.directory, 'cache')

    def unset_fsts(self):
        return [posmorph.unset_fsts() for posmorph in self.values()]

    def reset_fsts(self, fsts):
        for posmorph, f in zip(self.values(), fsts):
            posmorph.reset_fsts(f)

    def init_punc(self, chars, punc):
        '''Make punctuation regular expression objects and substitution string.'''
        self.punc_after_re = re.compile(r'(' + chars + r')(' + punc + r')', re.U)
        self.punc_before_re = re.compile(r'(' + punc + r')(' + chars + r')', re.U)
        self.punc_sub = r'\1 \2'

    def sep_punc(self, text):
        """Separate punctuation from words."""
        text = self.punc_after_re.sub(self.punc_sub, text)
        text = self.punc_before_re.sub(self.punc_sub, text)
        return text

    def is_word(self, word, simple=False, ortho=True):
        """Is word an unanalyzable word?"""
        if ortho and word in self.punctuation:
            return word
        if ortho and not self.words:
            return None
        if not ortho and not self.words_phon:
            return None
        if ortho:
            word_rec = self.words[Morphology.simple if simple else Morphology.complex]
            return word in word_rec and word
        else:
            word_rec = self.words_phon[Morphology.simple if simple else Morphology.complex]
            return word_rec.get(word, False)

    def set_words(self, filename='words.lex', ortho=True, simplify=False):
        '''Set the list/dict of unanalyzed words, reading them in from a file, one per line.'''
        if not ortho:
            filename = 'words_phon.lex'
        path = os.path.join(self.get_lex_dir(), filename)
#        path = os.path.join(self.directory, filename)
        position = Morphology.simple if simplify else Morphology.complex
        if os.path.exists(path):
            file = open(path, encoding='utf8')
            if ortho:
                # Read in the words as a list
                self.words[position] = [w.strip() for w in file]
            else:
                # Read in ortho:phon pairs as a dict
                self.words_phon[position] = dict([w.split() for w in file])
            file.close()
        else:
            self.words = []
            self.words_phon = []

    def get_analyzed(self, word):
        '''Get the pre-analyzed FS for word.'''
        return self.analyzed.get(word)

    def set_analyzed(self, filename='analyzed.lex', ortho=True, verbose=False):
        '''Set the dict of analyzed words, reading them in from a file, one per line.'''
        if not ortho:
            filename = 'analyzed_phon.lex'
        path = os.path.join(self.get_lex_dir(), filename)
#        path = os.path.join(self.directory, filename)
        if os.path.exists(path):
            file = open(path, encoding='utf8')
            if verbose:
                print('Storing pre-analyzed forms')
            if ortho:
                for line in file:
                    # Word and FS separated by two spaces
                    word, anal = line.split('  ')
                    fs = FSSet.parse(anal.strip())
                    self.analyzed[word] = fs
            else:
                for line in file:
                    # Word and FS separated by two spaces
                    word, phon, anal = line.split('  ')
                    fs = FSSet.parse(anal.strip())
                    self.analyzed_phon[word] = (phon, fs)
            file.close()

##    def set_fsh(self, *label_fs):
##        """Set the Feature Structure Hierarchy for this language's morphology."""
##        self.fsh = FSHier()
##        self.fsh.parse(label_fs)

    def trivial_anal(self, form):
        """Attempt to trivially analyze form."""
        return self.triv_anal and self.triv_anal(form)

    def anal(self, form, pos, to_dict=True, preproc=False, guess=False, phon=False, segment=False,
             trace=False, tracefeat=''):
        return self[pos].analyze(form, to_dict=to_dict, preproc=preproc, guess=guess, phon=phon, segment=segment,
                                 trace=trace, tracefeat=tracefeat)

    def gen(self, form, features, pos, guess=False, phon=False, segment=False,
            trace=False):
        return self[pos].gen(form, features, guess=guess, phon=phon, segment=segment, trace=trace)

    def load_fst(self, label, generate=False, create_fst=True, save=False, verbose=False):
        """Load an FST that is not associated with a particular POS."""
        path = os.path.join(self.directory, label + '.cas')
        casc = fst = None
        if verbose: print('Looking for cascade at', path)
        if os.path.exists(path):
            # Load each of the FSTs in the cascade and compose them
            if verbose: print('Loading cascade...')
            casc = FSTCascade.load(path, seg_units=self.seg_units,
                                   create_networks=True)
            # create_fst is False in case we just want to load the individuals fsts.
            if create_fst:
                if verbose:
                    print("Composing FST")
                fst = casc.compose(backwards=True, trace=verbose, relabel=True)
                if generate:
                    fst = fst.inverted()
                if save:
                    FST.write(fst, filename=os.path.join(self.directory, label + '.fst'))
                return fst
            return casc

#    def restore_fst(self, label):
#        '''Return the FST with label.'''
#        print("Restoring FST {}".format(label))
#        cas_path = os.path.join(self.directory, label + '.cas')
#        cascade = None
#        if os.path.exists(cas_path):
#            cascade = FSTCascade.load(cas_path,
#                                      seg_units=self.seg_units, create_networks=True,
#                                      verbose=False)
#        if cascade != None:
#            # Look for the full, explicit FST
#            fst_file = label + '.fst'
#            fst_path = os.path.join(self.directory, fst_file)
#            if os.path.exists(fst_path):
#                return FST.restore_parse(self.directory, fst_file, cascade=cascade,
#                                         weighting=UNIFICATION_SR,
#                                         seg_units=self.seg_units,
#                                         create_weights=True)

    def sort_analyses(self, analyses):
        """Each analysis is a root, fs pair. Sort by the list of values for each feature that has such a list.
        SEVERAL THINGS DON'T WORK HERE. FIRST ANALYSES SHOULD BE SORTED BY THE *SUM* OF THE SCORES FOR EACH
        FEATURE. SECOND, EMBEDDED FEATURE VALUES DON'T WORK YET."""
        for pos, morph in self.items():
            feat_list = morph.feat_list
            for feat, values in feat_list:
                # Features associated with the POS FST
                if isinstance (values, (list, FeatStruct)):
                    continue
                self.sort_analyses1(analyses, pos, feat, values)

    def sort_analyses1(self, analyses, pos, feat, values):
        def anal_index(analysis):
            root, anal = analysis
            anal_pos = anal.get('pos', 'v')
            if anal_pos != pos:
                return 100
            else:
                value = anal.get(feat)
                if value:
                    if value not in values:
                        print("{} not in {}".format(value, values))
                        return 100
                    return values.index(value)
                return 100
        analyses.sort(key=lambda a: anal_index(a))

##    def load_phon_fst(self, save=True, verbose=True):
##        """Load the phon FST if there is one."""
##        cascade = FSTCascade.load(os.path.join(self.directory, 'phon.cas'),
##                                  seg_units=self.seg_units, create_networks=True,
##                                  verbose=verbose)
##        if cascade:
##            fst = cascade.compose(backwards=True, trace=verbose)
##            if fst:
##                fst = fst.inverted()
##                if save:
##                    FST.write(fst, filename=os.path.join(self.directory, 'phon.fst'), shelve=False)
##                    self.phon_fst = fst
##                return fst

##    def ortho2phon(self, word):
##        '''Attempt to convert a word to its phonetic form. (Assumes word is already romanized.)'''
##        if word.isdigit():
##            # word consists only of numbers
##            return [word]
##        if self.words_phon:
##            words = self.words_phon[Morphology.complex]
##            if not isinstance(words, dict):
##                print('Words dict is not loaded!')
##                return
##            phon = words.get(word, '')
##            if phon:
##                return [phon]
##        elif word in self.analyzed_phon:
##            form, fss = self.analyzed_phon[word]
##            return [form]
##
##    def phonetic(self, form):
##        '''Make a form phonetic, calling the phon FST on it.'''
##        fst = self.phon_fst
##        if fst:
##            phoneticized = fst.transduce(form, seg_units=self.seg_units)
##            if phoneticized:
##                return phoneticized[0][0]
##        return form

class POS:
    """FSTs and lex lists for analysis and generation of words in a particular POS class."""

    def __init__(self, pos, language, fullname=''):
        # A string representing part of speech
        self.pos = pos
        self.fullname = fullname
#        # Weight constraint on FST arcs
#        self.wc = None if pos == 'all' else FSSet('[pos=' + pos + ']')
        # The string used as type in FSs
        self.type = '%' + pos
        self.language = language
        ## FSTs
        # Analysis FST
        self.anal_fst = None
        # Guesser analysis FST
        self.anal_guess = None
        # Generation FST
        self.gen_fst = None
        # Segmentation FST
        self.seg_fst = None
        # Guesser segmentation FST
        self.seg_guess = None
        # Default FS for generation
        self.defaultFS = TOP
        # Default FS for citation
        self.citationFS = TOP
        # Dictionary of FS implications
        self.FS_implic = {}
        ## Functions
        # Analysis to string
        self.anal2string = None
        # Dict of common and irregular analyzed words for analysis
        self.analyzed = {}
        # Reverse dict for analyzed words, used in generation (derived from self.analyzed)
        self.generated = {}
        # Dict of possible grammatical features and their values
        self.features = {}
        # List of features and possible values
        self.feat_list = None
        self.gen_fvs = []
        ## Morph feat to morph value, syn feat/value dict for analysis.
        ## Differs from this class in L3Morph!
        self.anal_dict = {}
        ## Syn feat to syn value, morph feat/value dict for generation
        self.gen_dict = {}
        ## Feature and value abbreviation dict
        self.abbrevs = {}
        ## Reverse abbreviation dict
        self.rev_abbrevs = {}
        ## FS abbreviation list
        self.fv_abbrevs = []
        self.fv_priority = []
        self.excl_feats = []
        ## Features to include in pretty analysis output
        self.explicit_feats = []
        ## Features to include in pretty analysis output only if they're not False or None
        self.true_explicit_feats = []
        ## Generation cache
        self.gen_cached = {}
        # New generations since language loaded, each entry a (root FS) pair and a list of words
        self.new_gens = {}

    def quit(self):
        """Save new_gens in gen_cache."""
        self.write_gen_cache()

    def make_rev_abbrevs(self):
        """Make the reverse abbreviation dictionary."""
        for ab, full in self.abbrevs.items():
            self.rev_abbrevs[full] = ab

#    def unset_fsts(self):
#        tmp_fsts = self.fsts
#        self.fsts = [[None, None, None, None, None, None], [None, None, None, None, None, None]]
#        return tmp_fsts

#    def reset_fsts(self, fsts):
#        self.fsts = fsts

    def get_gen_fvs(self):
        """The features and their values that are used for generation."""
        if self.gen_fvs:
            return self.gen_fvs
        fvdict = dict(self.feat_list)
        for f in self.explicit_feats:
            values = fvdict[f]
            vals = []
            for v in values:
                if isinstance(v, str):
                    vals.append(self.exab(v))
                elif isinstance(v, tuple):
                    vals.append((self.exab(v[0]), v[1]))
                else:
                    vals.append(v)
            self.gen_fvs.append((self.exab(f), vals))
        return self.gen_fvs

    def get_fst(self, generate=False, guess=False, segment=False):
        """The FST satisfying the parameters."""
        if generate:
            return self.gen_fst
        if segment:
            if guess:
                return self.seg_guess
            else:
                return self.seg_fst
        if guess:
            return self.anal_guess
        return self.anal_fst

    def set_fst(self, fst, generate=False, guess=False, segment=False):
        """Assign the FST satisfying the parameters."""
        if generate:
            self.gen_fst = fst
        elif segment:
            if guess:
                self.seg_guess = fst
            else:
                self.seg_fst = fst
        elif guess:
            self.anal_guess = fst
        else:
            self.anal_fst = fst
        # Also assign the defaultFS if the FST has one
        if fst._defaultFS:
            self.defaultFS = fst._defaultFS

    def fst_name(self, generate=False, guess=False, segment=False):
        """Make a name for the FST satisfying the parameters."""
        pos = self.pos
        if generate:
            return pos + 'G'
        if guess:
            pos += '0'
        if segment:
            return pos + '+'
        return pos

    def get_analyzed(self, word, sep_anals=False, pretty=False):
        """Stored analysis of word if there is one."""
        if self.analyzed:
            anals = self.analyzed.get(word, None)
            if anals and sep_anals:
                root = anals[0]
                gram = anals[1]
                if pretty:
                    gram = [self.fs2prettylist(g) for g in gram]
                    anals = [(root, self.fullname, g) for g in gram]
                else:
                    anals = [(root, g) for g in gram]
            return anals

    def set_analyzed(self, filename='analyzed.lex', verbose=False):
        '''Set the dicts of analyzed words for analysis and generation,
        reading them in from a file, one per line.'''
        path = os.path.join(self.language.get_lex_dir(), self.pos + '_' + filename)
        if os.path.exists(path):
            file = open(path, encoding='utf8')
            if verbose:
                print('Storing irregular pre-analyzed forms:', self.pos)
            for line in file:
                # For ortho=True, each line is
                # word  root  FSS
                # For ortho=False, each line is
                # word phon root FSS
                split_line = line.partition(' ')
                word = split_line[0]
                split_anal = split_line[2].strip().partition(' ')
                root = split_anal[0]
                fs = split_anal[2]
                if word and fs:
                    if not root:
                        root = word
                    fs = FSSet.parse(fs)
                    self.analyzed[word] = [root, fs]
            file.close()
#        else:
#            print("No analyzed forms found for", self.pos)

    def get_features(self):
        '''Get the dict of grammatical features and values, generating it if {}.'''
        if not self.features:
            fst = self.get_fst()
            if fst:
                self.features = fst.get_features()
        return self.features

#    def has_cas(self, generate=False, simplified=False, guess=False,
#                phon=False, segment=False):
#        """Is there a cascade file for the given FST features?"""
#        name = self.fst_name(generate=generate, simplified=simplified,
#                             guess=guess, phon=phon, segment=segment)
#        path = os.path.join(self.morphology.directory, name + '.cas')
#        return os.path.exists(path)

    def get_gen_cache_file(self, name=''):
        d = self.language.get_cache_dir()
        if name == True or not name:
            name = self.pos
        return os.path.join(d, name + '.gch')

    def add_new_gen(self, root, fs, words, verbose=0):
        if (root, fs) not in self.new_gens:
            if verbose:
                print("Adding new gen {}:{} || {}".format(root, fs.__repr__(), words))
            self.new_gens[(root, fs)] = words

    def get_cached_gen(self, root, fs):
        """Returns cached words for root, FS pair, if any."""
        if isinstance(fs, FeatStruct) and not fs.frozen():
            fs.freeze()
#        print("Root {}, FS {}".format(root, fs.__repr__()))
        if (root, fs) not in self.gen_cached:
            return False
        else:
            return self.gen_cached[(root, fs)]

    def write_gen_cache(self, name=''):
        """Write a dictionary of cached entries to a gen cache file. This should only be used in
        combination with only_words=True in gen() so that no analyses are included."""
        if self.new_gens:
            # Only attempt to cache generations if there are new ones.
            file = self.get_gen_cache_file(name=name)
            with open(file, 'a', encoding='utf8') as out:
                for (root, fs), words in self.new_gens.items():
                    print("{}:{} || {}".format(root, fs.__repr__(), ';'.join(words)), file=out)
        # Empty new_gens in case we want to add things later
        self.new_gens.clear()

    def read_gen_cache(self, name=''):
        """Read cached entries into self.gen_cached from a file."""
        file = self.get_gen_cache_file(name=name)
        try:
            with open(file, encoding='utf8') as f:
#                print("Leyendo archivo almacenado de generación para {}".format(self.pos))
                for line in f:
                    root_fs, words = line.strip().split(" || ")
                    root, fs = root_fs.split(':')
                    words = words.split(';')
                    if fs in ('[]', 'None'):
#                        fs = TOP
                         fs = None
                    else:
                        fs = FeatStruct(fs, freeze=True)
                    self.gen_cached[(root, fs)] = words
        except IOError:
            print('No such gen cache file as {}'.format(file))

    def load_fst(self, generate=False, guess=False, segment=False,
                 verbose=False):
        '''Load FST.'''
        fst = None
        if verbose:
            s1 = '\nAttempting to load {0} FST for {1} {2}{3}{4}'
            print(s1.format(('GENERATION' if generate else 'ANALYSIS'),
                            self.language.name, self.pos,
                            (' (GUESSER)' if guess else ''),
                            (' (SEGMENTED)' if segment else '')))
        # Load a composed FST encompassing everything in the cascade
        fst = FST.restore(self.pos, self.language.get_fst_dir(),
                          seg_units=self.language.seg_units,
                          create_weights=False, generate=generate,
                          empty=guess, segment=segment, verbose=verbose)
        if fst:
            if verbose: print("Found FST")
            self.set_fst(fst, generate, guess, segment=segment)
        else:
            if verbose: print("Found no FST")
        if self.get_fst(generate, guess, segment=segment):
            # FST found one way or another
            return True

    def save_fst(self, generate=False, guess=False, 
                 phon=False, segment=False, features=True):
        '''Save FST in a file.'''
        fname = self.fst_name(generate=generate, guess=guess, phon=phon, segment=segment)
        extension = '.fst'
        fst = self.get_fst(generate=generate, guess=guess, segment=segment)
        directory = self.morphology.directory
        FST.write(fst, filename=os.path.join(directory, fname + extension),
                  features=features, exclude_features=['t', 'm'])

    def unsave_fst(self, fst_file=True):
        '''Get rid of saved FSTs.'''
        if fst_file:
            os.remove(os.path.join(self.morphology.directory, self.pos + '.fst'))

    def analyze(self, form, to_dict=False, preproc=False,
                guess=False, segment=False, sep_anals=False,
                timeit=False, trace=False, tracefeat='',
                # whether to replace FSs with "pretty" feature-value lists
                pretty=False):
        """Analyze form."""
        fst = self.get_fst(generate=False, guess=guess, segment=segment)

        if fst:
#            if preproc:
#                # For languages with non-roman orthographies
#                form = self.morphology.language.preprocess(form)
            # If result is same as form and guess is True, reject
            anals = fst.transduce(form, seg_units=self.language.seg_units, reject_same=guess,
                                  trace=trace, tracefeat=tracefeat, timeit=timeit)
            if sep_anals:
                anals = self.separate_anals(anals)
                if pretty:
                    anals = self.prettify_analyses(anals)
            if to_dict and not pretty:
                anals = self.anals_to_dicts(anals)
            return anals
        elif trace:
            print('No analysis FST loaded for', self.pos)

    def separate_anals(self, analyses):
        """Separate list of root and FSSets into a list of roots and FeatStructs."""
        result = []
        for root, anals in analyses:
            for anal in anals:
                result.append((root, anal))
        return result

    def gen(self, root, features=None, update_feats=None,
            guess=False, segment=False, fst=None, timeit=False, only_one=False, cache=True,
            # Return only word forms
            only_words=True,
            trace=False):
        """Generate word from root and features."""
#        print("Update feats {}, type {}".format(update_feats, type(update_feats)))
        if isinstance(update_feats, str):
            update_feats = FeatStruct(update_feats)
        # See if there are already cached wordforms for the root and features
        cache_keys = []
        if isinstance(update_feats, FSSet):
            cache_keys = list(update_feats)
        else:
            cache_keys.append(update_feats)
        all_cached = []
        for cache_key in cache_keys:
            cached = self.get_cached_gen(root, cache_key)
            if cached:
                all_cached.extend(cached)
        if all_cached:
            if trace:
                print("Found {}:{} in cached generations".format(root, cache_keys))
            return all_cached
        features = features or self.defaultFS
        upd_features = features
        if update_feats:
            if isinstance(update_feats, FSSet):
                upd_features = self.update_FSS(FeatStruct(features), update_feats)
            else:
                upd_features = self.update_FS(FeatStruct(features), update_feats)
        fst = fst or self.get_fst(generate=True, guess=guess, segment=segment)
        if not fst:
            return []
        # Up to this point, features may be a FeatStruct instance; cast in case
        fsset = FSSet.cast(upd_features)
        if fst:
            gens = fst.transduce(root, fsset, seg_units=self.language.seg_units, trace=trace, timeit=timeit)
            if only_words:
                gens = [g[0] for g in gens]
            if cache and gens:
                for cache_key in cache_keys:
                    self.add_new_gen(root, cache_key, gens)
            return gens
        elif trace:
            print('No generation FST loaded')
            return []

    def anals_to_dicts(self, analyses):
        '''Convert list of analyses to list of dicts.'''
        dicts = []
        for anal in analyses:
            root = anal[0]
            for fs in anal[1]:
                dicts.append(self.anal_to_dict(root, fs))
        return dicts

    def anal_to_gram(self, anal, gen_root=None):
        """Convert an analysis into a list of lists of morphs and grams."""
        gram = []
        for a in anal:
            # A single root, possibly multiple fss
            root = gen_root or a[0]
            # FeatStruct set
            for fs in a[1]:
                gram.append((self.fs_to_morphs(root, fs),
                             self.fs_to_feats(root, fs),
                             a[0]))
        return gram

    def segment(self, word, seg, feature, value, new_value=None):
        """If feature has value in word, segment the word into seg
        and the word with feature changed to new_value."""
        anals = self.anal(word)
        segmentations = []
        for anal in anals:
            for a in anal:
                segmented = self.segment1(feature, value, a, new_value=new_value)
                if segmented:
                    segmentations.append((segmented, seg))
        return segmentations

    def segment1(self, feature, value, analysis, new_value=None):
        root, a = analysis
        print('a {}'.format(a.__repr__()))
        if a.get(feature) != value:
            return
        # only work with the first FS
#        a = list(a)[0]
        a = a.unfreeze()
        a[feature] = new_value
        new_word = self.gen(root, features=a)
        if new_word:
            # only use the first generated word
            return new_word[0][0]

    def update_FSS(self, fs, feat_fss, top=True):
        """Starting with a FeatStruct fs, update it using the features in FSSet feat_fss,
        resulting in an FSSet."""
        fss = set()
        for feat_fs in feat_fss:
            fs1 = self.update_FS(fs, feat_fs, top=top)
            fs1.freeze()
            # Assume this always results in a non-zero FeatStruct
            fss.add(fs1)
        return FSSet(fss)

    def update_FS(self, fs, features, top=True):
        """Add or modify features (a FS, FSSet, dict, or string) in fs."""
        fs = fs.copy()
        # First make sure features is a FeatStruct
        if isinstance(features, str):
            features = FeatStruct(features)
        for key, value in features.items():
            # Make True any features that are implied by key
            implications = self.FS_implic.get(key, [])
            # All of the implications associated with key
            for implic in implications:
                # Implications that are not represented as lists just mean
                # to make that feature True
                # (Make sure the feature doesn't have an explicit value)
                if not isinstance(implic, list) and not isinstance(implic, tuple) \
                        and implic not in features:
                    fs.update({implic: True})
            # Complex feature in features
            if hasattr(value, 'keys'):
                # value is a mapping
#            if isinstance(value, FeatStruct):
                # Recursively update value with value in fs for key
                if key not in fs:
                    return []
                value = self.update_FS(fs.get(key), value, top=False)
                # And make True any features that must be True in value
                for implic in implications:
                    if isinstance(implic, list):
                        for imp in implic:
                            # Make sure the feature doesn't have an explicit value
                            if imp not in value:
                                value.update({imp: True})
            fs.update({key: value})
        # Finally check all of the key, value pairs in self.FS_implic for
        # which the key is a tuple: (feat, value)
        if top:
            for key, implics in self.FS_implic.items():
                if isinstance(key, tuple):
                    # See whether this tuple represents the value of a feature
                    # in features
                    key_values = key[1]
                    # Could be a string or a list of strings; make sure it's a list
                    if not isinstance(key_values, tuple):
                        key_values = (key_values,)
                    if features.get(key[0], 'missing') in key_values:
                        # If so, apply the constraints, as long as they're not
                        # overridden by an explicit value in features
                        for f, v in implics:
                            # If v is a list, then make the value of the listed
                            # item in the list in fs[f] True
                            if isinstance(v, list):
                                if f in features and v[0] in features[f]:
                                    continue
                                fs[f][v[0]] = True
                            # If v is is tuple, then make the value of the item
                            # in the tuple False
                            elif isinstance(v, tuple):
                                if f in features and v[0] in features[f]:
                                    continue
                                fs[f][v[0]] = False
                            elif f not in features:
                                # Otherwise treat f as feature, v as value in fs
                                fs[f] = v
        return fs

    def gen_citation(self, root, fs):
        if self.citationFS == '[]':
            return root
        # Return root if no citation is found
        result = root
        # Unfreeze the feature structure
        fs = fs.unfreeze()
        # Update the feature structure to incorporate default (with or without vc and as)
        fs.update(self.citationFS)
        # Refreeze the feature structure
        fs.freeze()
        # Find the first citation form compatible with the updated feature structure
        citation = self.gen(root, fs)
        if citation:
            result = citation[0][0]
        return result

    def prettify_analyses(self, analyses):
        """analyses a list of (root, FS) analyses."""
        return [(analysis[0], self.fullname, self.fs2prettylist(analysis[1])) for analysis in analyses]

    def fs2prettylist(self, fs):
        """Convert a FS to a list with abbreviations and feature combinations spelled out."""
        l = []
        # Go through the explicit features, recording all that appear in the FS
        # Preserves the order that features appear in .lg file
        for feat in self.explicit_feats:
            if feat not in fs:
                continue
            val = fs[feat]
            if not val and feat in self.true_explicit_feats:
                continue
#        for feat, val in fs.items():
#            if feat == 'pos':
#                continue
#            if feat not in self.abbrevs:
#                continue
            if val is True:
                l.append((self.exab(feat), '+'))
            elif val is False:
                l.append((self.exab(feat), '-'))
            else:
                f, v = self.fval_pair(feat, val)
                if v:
                    l.append((f, v))
#        # Sort alphabetically by feature name
#        l.sort()
        return l

    def fval_pair(self, feat, val):
        """Convert feat, val pair to a pretty pair, expanding abbreviations."""
#        if isinstance(val, bool):
#            return self.exab(feat), val
#            return '{}{}'.format('+' if val else '-', self.exab(feat))
        if isinstance(val, FeatStruct):
            valexpanded = self.expfv(val)
#            print('val {}, valexpanded {}'.format(val.__repr__(), valexpanded))
            v = valexpanded[0][0] if valexpanded[0] else None
            if v is False:
                return feat, ''
            if not v:
                # Record all features in val that are not False
                v = []
                for ft, vl in val.items():
                    if vl:
                        v.append(self.exab(ft))
                if v:
                    # Sort features some other way here?
                    v.sort()
                    # Convert list of recorded features to a comma-separated string
                    v = ', '.join(v)
            return self.exab(feat), v
        else:
            return self.exab(feat), self.exab(val)
#            return '{} = {}'.format(self.exab(feat), self.exab(val))

    def expfv(self, fs):
        '''Find feature value sets that have special names (expansions).'''
#        print('fs {}'.format(fs.__repr__()))
        expansions = []
        feats_used = []
        for fvs in self.fv_priority:
            match = True
            for f, v in fvs:
                if f not in fs or fs[f] != v:
                    match = False
                    break
            if match:
                # Found a fv combination with priority; look up its expansion
                # in fv_abbrevs
                expansion = some(lambda x: x[1] if x[0] == fvs else False, self.fv_abbrevs)
                return [expansion], True
        for fvs, exp in self.fv_abbrevs:
            match = True
            if all([(fv[0] in feats_used) for fv in fvs]):
                continue
            for f, v in fvs:
                if f not in fs or fs[f] != v:
                    match = False
                    break
            if match:
                if exp:
                    # If any feature combination has 'None', etc. as expansion,
                    # don't go any further
                    if exp in ['None', 'False', 'Null']:
                        return [False], []
                    # The expansion may be empty
                    expansions.append(exp)
                feats_used.extend([fv[0] for fv in fvs])
#        print('expfv {}, {}'.format(expansions, feats_used))
        return expansions, feats_used

    def exab(self, string):
        """Just a short form for expand_abbrev."""
        return self.abbrevs.get(string, string)

    def exrevab(self, string):
        """Just a short form for expand rev abbrev."""
        return self.rev_abbrevs.get(string, string)

    def __str__(self):
        '''Print name.'''
        return self.pos + '_morphology'

    def __repr__(self):
        '''Print name.'''
        return self.pos + '_morphology'

