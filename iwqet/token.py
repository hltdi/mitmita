#
#   Mit'mit'a
#   Mbojereha tokens in entries, etc.
########################################################################
#
#   This file is part of the PLoGS project
#   for parsing, generation, translation, and computer-assisted
#   human translation.
#
#   Copyleft 2020 HLTDI, PLoGS <gasser@indiana.edu>
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

# 2020.10.9
# -- Split off from entry.py

class Token:
    """Word or punctuation or category or POS within a sentence or entry."""

    spec_char = '%'
    cat_char = '$'
    set_char = '$$'
    pos_char = '&'
    spec_sep_char = '~'
    del_char = '~'
    ungen_char = '*'
    add_char = "+"

    def __init__(self, name='', prefix='', parent=None):
        self.name = name
        self.prefix = prefix
        self.parent = parent
        if prefix:
            self.fullname = prefix + Token.spec_sep_char + name
        else:
            self.fullname = name

    def __repr__(self):
        return self.name

    ## Static methods operating on strings that include the prefixes and
    ## names of Tokens.

    @staticmethod
    def is_special(token):
        """token is the prefix+name of a Token (not necessarily
        instantiated), or just the prefix.
        True if this is a 'special' token (name, number, etc.)"""
        return token and token[0] == Token.spec_char

    @staticmethod
    def is_cat(token):
        """Is this the name of a category?"""
        return Token.cat_char in token

    @staticmethod
    def is_set(token):
        """Is this the name of a set (implemented as a category)?"""
        return Token.set_char in token

    @staticmethod
    def is_pos(token):
        """Is this the name of a POS?"""
        return token[0] == Token.pos_char

    @staticmethod
    def is_ungen(token):
        """Is this the root of a failed morphological generation?"""
        return token[0] == Token.ungen_char

    @staticmethod
    def is_target(token):
        """Is this an introduced target language token?"""
        return token[0] == Token.add_char

    @staticmethod
    def is_root(token):
        """
        Is this a noun, verb, or adjective root?
        Does it contain '_', and is the part after '_' non-empty?
        """
        return '_' in token and token.split('_')[-1]

    @staticmethod
    def special_prefix(token, check=False):
        """If this is a special token, return its prefix (what precedes ~)."""
        if not check or Token.is_special(token):
            return Token.split_token(token)[0]
        return ''

    @staticmethod
    def del_token(token):
        return token and token[0] == Token.del_char

    @staticmethod
    def special_cat(prefix):
        """Return the category of a special prefix: C or N."""
        if Token.is_special(prefix):
            return prefix.split(Token.spec_char)[-1]
        return None

    @staticmethod
    def split_token(token):
        """Separate the prefix and the name from the token string.
        The first instance of ~ connects the prefix to the name for a special token.
        There can be more than one ~ in numerals."""
        if Token.spec_sep_char in token:
            prefix, x, name = token.partition(Token.spec_sep_char)
        else:
            prefix = ''
            name = token
        return prefix, name

class RootToken(Token):
    """
    Root tokens, e.g., sbr_v.
    """

    @staticmethod
    def get_POS(token):
        """Token may be something like guata_, guata_v, ber__n."""
        if Token.is_special(token) or '_' not in token:
            return token, None
        for pos in ['v', 'a', 'n', 'nm', 'n_v', 'cop', 'nm_pl', 'nm_prs']:
            if token.endswith('_' + pos):
                root, p, x = token.rpartition('_' + pos)
                return root, pos
        return token, None

class SentToken(Token):
    """Sentence tokens."""

    def __init__(self, name='', prefix='', parent=None,
                 punc=False, upper=True):
        Token.__init__(self, name=name, prefix=prefix, parent=parent)
        if Token.spec_char in prefix:
            self.special = True
            self.raw_prefix = prefix[1:]
        else:
            self.special = False
            self.raw_prefix = prefix
        self.in_sentence = True
        self.in_entry = False
        self.cat = False
        self.set = False
        self.punc = punc
        self.delete = False
        self.upper = upper

    def __repr__(self):
        prechar = "<"
        postchar = ">"
#        if self.prefix:
#            return prechar + self.fullname + postchar
#        else:
        return prechar + self.fullname + postchar

    @staticmethod
    def is_name_token(token):
        """Name tokens are capitalized but not all uppercase."""
        if not self.upper:
            return False
        if len(token) > 0:
            if token[0].isupper():
                if len(token) == 1 or not token.isupper():
                    return True
        return False

    def get_keys(self, index=0):
        """Keys for finding group candidates."""
        keys = {self.name}
        if self.special:
            # Not sure if any groups are indexed by the fullname?
            keys.add(self.fullname)
        if index == 0 and self.upper:
            # First word in sentence
            keys.add(self.name.capitalize())
        return keys

class JoinToken(Token):
    """Token in join."""

    def __init__(self, name='', prefix='', parent=None, punc=False):
        Token.__init__(self, name=name, prefix=prefix, parent=parent)
        self.raw_prefix = prefix
        self.special = False
        self.pos = False
        self.cat = False
        if Token.spec_char in prefix:
            self.special = True
            self.raw_prefix = prefix[1:]
        elif Token.pos_char in prefix:
            self.pos = True
        elif Token.cat_char in prefix:
            self.cat = True
        self.in_sentence = False
        self.in_entry = True
        self.set = False
        self.punc = punc
        self.delete = False

    def __repr__(self):
        prechar = "<"
        postchar = ">"
        if self.prefix:
            return prechar + self.prefix + Token.spec_sep_char + self.name + postchar
        else:
            return prechar + self.name + postchar

    @staticmethod
    def match_pos(join_pos, seg_poss):
        """Does Join element POS match at least one of segment POSs?"""
#        print("Does joinpos {} match segposs {}".format(join_pos, seg_poss))
        for seg_pos in seg_poss:
            # seg_pos may include a sub_pos
            if '.' in seg_pos:
                seg_pos = seg_pos.split('.')[0]
            if join_pos == seg_pos:
                return True
        return False
