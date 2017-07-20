#   
#   MDT: loading and using external POS taggers
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
#
# 2017.4.13: Created
# 2017.4.16:
# -- Added class for NLTK English
# 2017.4.20:
# -- Lots of things fixed in NLTK class. It now uses nltk.word_tokenizer
#    for tokenization and then separates sentences on the basis of EOS
#    characters before using a Brill tagger to do POS tagging.
# 2017.4.22-4
# -- Switched to spaCy for English. Fixed what was needed to make that work.

import os
from mdt.morphology.semiring import FSSet

# Duplicated from language.py
LANGUAGE_DIR = os.path.join(os.path.dirname(__file__), 'languages')

def get_tagger(source, arg, lang_abbrev, conversion=None, lemmas=None, eos=None):
    if source == 'spacy':
        return Spacy(arg, lang_abbrev, conversion=conversion, eos=eos)
    elif source == 'nltk':
#        print("Loading NLTK tagger")
        return NLTK(arg, lang_abbrev, conversion=conversion, lemmas=lemmas, eos=eos)
    else:
        print("No external tagger in {} available for {}".format(source, lang_abbrev))

class Tagger:
    """Interface class for tokenizer/taggers."""

    def __init__(self, arg, lang_abbrev, conversion=None, lemmas=None, eos=None,
                 morph=False):
        self.lang = lang_abbrev
        self.conversion = conversion
        self.lemmas = lemmas
        self.eos = eos
        self.morph = morph

    def get_pos_conversion(self):
        return self.conversion[0]

    def get_feat_conversion(self):
        return self.conversion[1]

    @staticmethod
    def expand_POS(pos):
        """POS may have multiple segments, separated by .s"""
        return pos.split('.')

class NLTK(Tagger):
    """An object representing what a language needs to use the NLTK tokenizer and
    a trained Brill tagger within MDT."""

    def __init__(self, arg, lang_abbrev, conversion=None, lemmas=None, eos=None):
        # Morphological analysis is not needed for English but is for other languages?
        Tagger.__init__(self, arg, lang_abbrev, conversion=conversion,
                        lemmas=lemmas, eos=eos, morph=lang_abbrev != 'eng')
        from pickle import load
        import nltk
        import nltk.tbl
#        print("Loaded NLTK")
        pickle_path = os.path.join(os.path.join(os.path.join(LANGUAGE_DIR, lang_abbrev), 'syn'), "tag.pkl")
#        print("Pickle path {}".format(pickle_path))
        self.tokenizer = nltk.word_tokenize if lang_abbrev == 'eng' else None
#        print("Tokenizer: {}".format(self.tokenizer))
        self.tokenize = True if lang_abbrev == 'eng' else False
        with open(pickle_path, 'rb') as pkl:
            self.tagger = load(pkl)
#            print("Loaded tagger")

    def __repr__(self):
        return "NLTK:tagger:{}".format(self.lang)

    def tag(self, tokenized):
        """Tokenize and POS tag the text, returning a list of token, tag pairs."""
#        tokenized = self.tokenizer(text)
        return self.tagger.tag(tokenized)

    def get_lemma_features(self, item, mdt_feats=None):
        word, tag = item
        if not mdt_feats:
            mdt_feats = self.get_mdt_features(item)
        if not mdt_feats:
            return word.lower(), None
        lemma, features = mdt_feats
        if lemma == '=':
            lemma = word
        elif lemma == '*':
            # Look up the lemma in the lemma dictionary, return the word if nothing is found
            lemma = self.lemmas.get(word, word.lower())
        if features:
            # Make an actual FSSet
            features = FSSet(*features.split(';'))
        return lemma, features

    def get_repr(self, item):
        """The raw representation for tokens for MDT, providing the information that it needs for analyses."""
        pos = self.get_mdt_pos(item)
        pos_exp = Tagger.expand_POS(pos)
        short_pos = pos_exp[0]
        lemma, feats = self.get_lemma_features(item)
        token = item[0]
        root = lemma + '_' + short_pos
        return token, root, feats

    ## In the following, item is a token, POS pair

    def is_eos(self, item):
        return item[1].endswith('eos')

    def is_eos_tag(self, tag):
        return tag and 'eos' in tag

    def get_mdt_pos(self, item):
        pos = item[1]
        return self.get_pos_conversion().get(pos, '')

    def get_mdt_features(self, item):
        featconv = self.get_feat_conversion()
        tag = item[1]
        return featconv.get(item, featconv.get(('', tag)))

    def get_sentences(self, text):
        """Tokenize and tag the text if this hasn't happened already.
        Then split the resulting list into lists of sentence tuples."""
        if isinstance(text, str):
            # text needs to be tokenized, as well as tagged
            tokenized = self.tokenizer(text)
        else:
            # Text is already tokenized; this should already happened for languages
            # without external taggers, like Spanish (currently).
            tokenized = text
        sentences = []
        sentence = []
        # First separate text into sentences based on EOS characters
        for token in tokenized:
#            print("  Token {}".format(token))
            sentence.append(token)
            if token in self.eos:
#                print("    EOS, ending sentence")
                # End of a sentence
                sentences.append(sentence)
                sentence = []
        if sentence:
            sentences.append(sentence)
            sentence = []
        tagged_sents = []
#        print("Sentences: {}".format(sentences))
        # Now do POS tagging for each sentence
        for sentence in sentences:
            tagged = self.tag(sentence)
            repr = [self.get_repr(item) for item in tagged]
            tagged_sents.append([(word, {'root': root, 'features': feats}) for word, root, feats in repr])
#        print("Tagged sentences")
        for ts in tagged_sents:
            for items in ts:
                print(" {}".format(items))
            print()
        return tagged_sents

class Spacy(Tagger):
    """An object representing what a language needs to use the Spacy tagger within MDT."""

    def __init__(self, arg, lang_abbrev, conversion=None, eos=None):
        Tagger.__init__(self, arg, lang_abbrev, conversion=conversion, eos=eos, morph=False)
        import spacy
        print("spaCy imported")
        # No explicit tokenizer but the tagger itself tokenizes
        self.tokenizer = None
        self.tokenize = True
        # or spacy.load('en_depent_web_md') ??
        self.tagger = spacy.load('en_core_web_sm')
        print("spaCy tagger loaded")
#        self.tagger = spacy.load(arg)

    def __repr__(self):
        return "spaCy:tagger:{}".format(self.lang)

    def tag(self, text):
        """Tokenize and POS tag the text, returning a list of Tokens, returning a Spacy Doc instance, which
        (somehow) behaves like a list, at least supports indexing."""
        return self.tagger(text)

    def is_eos(self, item):
        return item.tag_ == '.'

    def get_pos(self, item):
        return item.pos_

    def get_mdt_pos(self, item):
        """POS appropriate for MDT."""
        pos = self.get_pos(item)
        return self.get_pos_conversion().get(pos, '')

    def get_mdt_features(self, item):
        """Feature string (not FeatStruct) for MDT."""
        featconv = self.get_feat_conversion()
        tag = self.get_tag(item)
        token = item.text
        mdt_feats = featconv.get((token, tag), featconv.get(('', tag)))
        if mdt_feats:
            lemma, features = mdt_feats
            if lemma == '=':
                lemma = token
            elif lemma == '*':
                lemma = self.get_lemma(item)
            if features:
                features = FSSet(*features.split(';'))
            return lemma, features
        else:
            return token, None

    def get_lemma(self, item):
        return item.lemma_

    def get_tag(self, item):
        return item.tag_

    def get_repr(self, item):
        """The raw representation for tokens for MDT."""
#        return item.text, self.get_lemma(item), self.get_pos(item), self.get_tag(item)
        return item.text, self.get_lemma(item), self.get_pos(item), self.get_tag(item), self.get_mdt_pos(item), self.get_mdt_features(item)
    
    def get_sentences(self, text):
        """Tokenize and tag the text if this hasn't happened already.
        Then split the resulting list into lists of sentence tuples."""
        if isinstance(text, str):
            # text needs to be tagged
            tagged = self.tag(text)
        else:
            tagged = text
        sentences = []
        sentence = []
        for item in tagged:
            itext, ilemma, ipos, itag, mpos, mfeats = self.get_repr(item)
            pos_exp = Tagger.expand_POS(mpos)
            short_pos = pos_exp[0]
            if ilemma[0] == '-':
                ilemma = itext
            if short_pos:
                root = ilemma + '_' + short_pos
            else:
                root = itext
            dct = {'root': root, 'pos': short_pos, 'features': mfeats[1]}
            sentence.append((itext, dct))
            if self.is_eos(item):
                sentences.append(sentence)
                sentence = []
        if sentence:
            # Last EOS token missing; call it a sentence anyway
            sentences.append(sentence)
        return sentences

    def get_featstring(self, item):
        pass

        
