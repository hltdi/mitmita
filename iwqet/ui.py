#   
#   Mainumby UI: initial attempt at a user interface for creating languages
#
########################################################################
#
#   This file is part of the HLTDI L^3 project
#   for parsing, generation, translation, and computer-assisted
#   human translation.
#
#   Copyright (C) 2014, 2016 HLTDI <gasser@indiana.edu>
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

# 2014.02.15
# -- Created
# 2014.03.04
# -- UI class
# 2014.03.18
# -- Adding groups
# 2015
# -- Needs to be updated to agree with new language and group features.

from .language import *
import os, sys

class UI:
    """Normally only one of these so doesn't have to be a class. Later a subclass
    of tkinter Frame?"""

    # Editing the grammar/lexicon
    edit_mode = 0
    # Parsing and translating
    proc_mode = 1
    
    def __init__(self):
        self.languages = {}
        self.mode = UI.edit_mode

    @staticmethod
    def yes(response):
        return not response or response[0].lower() == 'y'

    def load_language(self):
        abbrev = input("Give abbreviation for language.\n>> ")
        path = os.path.join(LANGUAGE_DIR, abbrev + '.lg')
        try:
            language = Language.read(path)
            self.languages[abbrev] = language
            return language
        except IOError:
            print("That language doesn't seem to exist.")
            return

    def quit(self):
        """Quit the UI (and L3Lite)."""
        response = input("Are you sure you want to quit L3Lite? ")
        if UI.yes(response):
            self.write_languages()
            sys.exit()

    def write_languages():
        """Write the languages the user wants to save."""
        for language in self.languages.values():
            if language.changed:
                response = input("{} has been changed; save?\n>> ".format(language.name))
            if UI.yes(response):
                language.write(LANGUAGE_DIR)

    def add_word(self, language):
        word = input("Write the word to be added to the lexicon.\n>> ")
        if word in language.words:
            response = input("There's already a word with that form in the lexicon; add another? ")
            if UI.yes(response):
                return self.add_word1(word, language)
            return
        else:
            return self.add_word1(word, language)

    def add_word1(self, word, language):
        cls = None
        response = input("Do you want to assign a class to the word? ")
        if UI.yes(response):
            class_names = list(language.classes.keys())
            cls = input("Choose from these classes:\n{}\n>> ".format(' '.join(class_names)))
        return language.add_word(word, cls=cls)

    def add_class(self, language):
        name = input("Write the name of the class to be added to the lexicon.\n>> ")
        if name in self.language.classes:
            response = input("There's already a class with that name in the lexicon; add a class with a different name? ")
            if UI.yes(response):
                return self.add_class1(name, language)
            return
        else:
            return self.add_class1(name, language)

    def add_class1(self, name, language):
        return language.add_class(name)

    def add_group(self, language):
        """Get the words that will be in the group. make_group() creates the group."""
        words = input(
        """Write the words, lexemes, or classes in the group in their typical order.
        Precede any lexemes with % and any classes with $. """)
        words = words.split()
        response = input("Are these the words you want in the group?\n{}\n".format(', '.join(words)))
        if UI.yes(response):
            return self.make_group(language, words)
        else:
            return self.add_group(language)

    def make_group(self, language, words, word_string=''):
        if not word_string:
            word_list = []
            for i, w in enumerate(words):
                word_list.append("[{}] {}".format(i+1, w))
            word_string = '\n'.join(word_list)
        head_index = input("Give the number of the word or lexeme that is the head of the group.\n{}\n>> ".format(word_string))
        if not head_index.isdigit():
            print("You need to give a number between 1 and {}".format(len(words)))
            return self.make_group(language, words, word_string=word_string)
        else:
            head_index = int(head_index)
            if head_index > len(words):
                print("You need to give a number between 1 and {}".format(len(words)))
                return self.make_group(language, words, word_string=word_string)
            else:
                head_index = head_index - 1
                head = words[head_index]
                name = '_'.join(words)
                print("OK, the head is '{}'".format(head))
                print("Creating group {} with head {}".format(name, head))
                group = language.add_group(name, head, head_lexeme=head.startswith(LEXEME_PRE), head_order=head_index)
                # A dictionary to associate order of words within the group with their IDs (indices).
                order2index = {head_index: 0}
                for index, word in enumerate(words):
                    if word == head:
                        continue
                    word_id = group.add_word(word, order=index)
                    order2index[index] = word_id
                response = input("Create dependencies among words?\n")
                if response:
                    return self.add_group_deps(group, word_string, order2index=order2index)
                else:  
                    return self.add_group_deps(group, word_string, first=False, finished=True, order2index=order2index)

    def add_group_deps(self, group, word_string, first=True, finished=False, order2index=None):
        if not first:
            if not finished:
                response = input("Finished with dependencies? ")
                if UI.yes(response):
                    finished = True
            if finished:
                for index, (lex, feats) in group.words.items():
                    # For each word in the group, make sure it's either
                    # the group head or that it has a mother within the
                    # group.
                    if index != 0 and 'm' not in feats:
                        print("Making word {} a daughter of head with default dependency".format(feats['o'] + 1))
                        group.add_dep(0, index)
                return group
            else:
                return self.add_group_dep(group, word_string, order2index=order2index)
        else:
            return self.add_group_dep(group, word_string, order2index=order2index)

    def add_group_dep(self, group, word_string, src_index=None, dest_index=None, order2index=None):
        if src_index is None:
            src_index = input("Give the index of the source word for a dependency.\n{}\n>> ".format(word_string))
            if not src_index.isdigit() or int(src_index) > len(group.words):
                print("You need to give a number between 1 and {}".format(len(group.words)))
                return self.add_group_dep(group, word_string, order2index=order2index)
            else:
                src_index = int(src_index) - 1
                if dest_index is None:
                    dest_index = input("Give the index of the destination word for the dependency.\n{}\n>> ".format(word_string))
                    if not dest_index.isdigit() or int(dest_index) > len(group.words):
                        print("You need to give a number between 1 and {}".format(len(group.words)))
                        return self.add_group_dep(group, word_string, src_index=src_index, order2index=order2index)
                    else:
                        dest_index = int(dest_index) - 1
                        dep = input("If you want a particular dependency type, enter it.\n>> ")
                        if not dep:
                            dep = Entry.dflt_dep
                        response = input("OK to create dependency of type {} from word {} to word {}?\n".format(dep, src_index + 1, dest_index + 1))
                        if UI.yes(response):
                            s = order2index[src_index]
                            d = order2index[dest_index]
                            # Actually create the dependency
                            group.add_dep(s, d, dep=dep)
                        return self.add_group_deps(group, word_string, first=False, order2index=order2index)

        
        
