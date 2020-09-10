# Mainumby. Parsing and translation with minimal dependency grammars.
#
########################################################################
#
#   This file is part of the PLoGS project
#   for parsing, generation, translation, and computer-assisted
#   human translation.
#
#   Copyleft 2019 PLoGS <gasser@indiana.edu>
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
# Created 2019.03.23
#
# class for storing variables needed in views.py

import re

from .utils import clean_sentence

from . import get_domains_texts

# the database class bound to the current app
from . import db, make_translation, make_dbtext

class GUI:

    # Compiled regexs for sentence cleaning
    clean_n = re.compile(r"\s+([.,;:?!)”″’%¶])")

    def __init__(self, list_texts=False):
        self.session = None
        self.user = None
        self.users_initialized = False
        # Source and target languages
        self.source = None
        self.target = None
        # TEXT (if document is stored in archive)
        self.textid = -1
        self.has_text = False
        # HTML for selecting text
        if list_texts:
            self.set_domains_texts()
        else:
            self.text_select_html = ''
        # DOCUMENT
        # The current document (if translating document)
        self.doc = None
        # HTML for the current document
        self.doc_html = None
        # HTML for already selected sentences
        self.doc_select_html = None
        # Translation HTML for sentences
        self.doc_tra_html = []
        # Translation strings, not necessarily accepted
        self.doc_tra = []
        # List of accepted translations of sentences in current doc
        self.doc_tra_acep = []
        # String concatenating accepted sentences
        self.doc_tra_acep_str = ''
        # Index of current sentence
        self.sindex = -1
        # SENTENCE
        # The current sentence
        self.sentence = None
        # Current raw sentence string
        self.fue = ''
        # HTML for the current source sentence
        self.fue_seg_html = None
        # Current sentence's segments (NOT ACTUALLY USED FOR ANYTHING CURRENTLY)
        self.segs = None
        # HTML for current sentence's segments
        self.tra_seg_html = None
        # Translation of the current sentence
        self.tra = None
        # TOGGLES: isdoc, nocorr, ocultar, sinopciones
        self.props = {}
        # Default
        self.props['tfuente'] = "115%"

    def init_doc(self):
#        self.doc_html = self.doc.select_html(index, self.fue_seg_html)
        nsent = len(self.doc)
        # List of translation HTML for sentences
        self.doc_tra_html = [""] * nsent
        # List of translation strings for sentences
        self.doc_tra = [""] * nsent
        # List of accepted translation strings for sentences
        self.doc_tra_acep = [""] * nsent
        # List of seg HTML for any selected sentences
        self.doc_select_html = [""] * nsent
        self.doc_html = self.doc.html
        self.doc_html_list = self.doc.html_list
        self.props['isdoc'] = True
        self.props['tfuente'] = "100%" if nsent > 1 else "115%"

    def init_text(self, textid, nsent, html, html_list):
#        print("Initializing text, nsent: {}".format(nsent))
        self.textid = textid
        self.has_text = True
        # List of translation HTML for sentences
        self.doc_tra_html = [""] * nsent
        # List of translation strings for sentences
        self.doc_tra = [""] * nsent
        # List of accepted translation strings for sentences
        self.doc_tra_acep = [""] * nsent
        # List of seg HTML for any selected sentences
        self.doc_select_html = [""] * nsent
        # HTML for source document
        self.doc_html = html
        self.text_html = html
        # List of HTML for each source sentence
        self.doc_html_list = html_list
        self.props['isdoc'] = True
        self.props['tfuente'] = "100%" if nsent > 1 else "115%"

    def doc_unselect_sent(self):
        # Revert to version of doc html with nothing segmented.
        if self.has_text:
            self.doc_html = self.text_html
        else:
            self.doc_html = self.doc.html

    def update_doc(self, index, choose=False, repeat=False):
        if repeat or choose:
            current_fue = self.doc_select_html[index]
        else:
            current_fue = self.fue_seg_html
#        print("Updating doc, current src {}".format(current_fue))
        self.doc_html = self.select_doc_html(index, current_fue)
        if not repeat:
            self.doc_select_html[index] = current_fue
        self.sindex = index

    def select_doc_html(self, index, shtml):
        """Replace the indexed element in html_list with one for the selected and translated
        element."""
        html = "<div id='doc'>"
        html_list = self.doc_html_list[:]
        html_list[index] = shtml
        html += "".join(html_list) + "</div>"
        return html

    def accept_sent(self, index, trans):
        """
        What happens when a sentence translation, part of a larger
        text, is accepted.
        """
        print("+++Adding accepted translation for position {}".format(index))
        # Update the accepted translations
        self.doc_tra_acep[index] = trans
#        print("+++New doctrans: {}".format(self.doc_tra_acep))
        # Return a string concatenating all accepted translations
        self.doc_tra_acep_str = self.stringify_doc_tra()
#        "\n".join([t for t in self.doc_tra_acep if t]).strip()
        self.doc_unselect_sent()
        print("+++New trans string: {}".format(self.doc_tra_acep_str))
        self.props['tfuente'] = "100%"

    def stringify_doc_tra(self):
        """Create a string representation of the currently accepted sentence translations.
        Probably need to make the more efficient by saving series of consecutive sentences
        that have already been stringified."""
        string = ''
        for sent_trans in self.doc_tra_acep:
            if not sent_trans:
                continue
            if "¶" == sent_trans[-1]:
#                print("Paragraph in {}".format(sent_trans))
                # New paragraph after this sentence
                # Replace the ¶ with a newline
                sent_trans = sent_trans.replace("¶", "\n")
            else:
                sent_trans += " "
            string += sent_trans
        return string.strip()

    def init_sent(self, index, choose=False, isdoc=False, trans='', source=''):
        """What happens after a sentence has been translated."""
        cap = self.sentence.capitalized
        self.props['cap'] = cap
        self.props['punc'] = self.sentence.get_final_punc()
        if choose:
            self.fue = source
            self.tra = trans
            self.fue_seg_html = ''
            self.doc_tra_html[index] = ''
            self.doc_tra[index] = self.tra
        else:
            self.fue_seg_html = ''.join([s[-1] for s in self.tra_seg_html])
            self.tra = clean_sentence(' '.join([s[4] for s in self.tra_seg_html]), cap)
#        GUI.clean_sentence(' '.join([s[4] for s in self.tra_seg_html]), cap)
            if isdoc:
                self.doc_tra_html[index] = self.tra_seg_html
#        print("New tra seg: {}".format(self.tra_seg_html))
                self.doc_tra[index] = self.tra

    def clear(self, record=False, translation='', isdoc=False, tradtodo=False,
              abandonar=False):
        """
        Clear all document and sentence variables, and record the current
        translation if record is True and there is a translation. If tradtodo
        is True, keep the doc, doc_html, textid.
        """
        if record and translation:
            # there could be line feed characters
            translation = translation.replace("\r", "")
            translation = translation.split("\n")
            print("Recording translation {}".format(translation))
            if not self.has_text:
                print("GUI doc {}".format(self.doc))
                docconts = '\n'.join([s.original for s in self.doc])
                text = make_dbtext(docconts, self.source, segment=True)
                textid = -1
            else:
                text=None
                textid = self.textid
            make_translation(text=text, textid=textid, user=self.user,
                             translation=translation,
                             accepted=self.doc_tra_acep)
        sentrec = None
        if self.sentence:
            sentrec = self.sentence.record
        self.tra_seg_html = None
        self.sentence = None
        if not abandonar:
            self.has_text = False
#        if not tradtodo:
        self.textid = -1
        self.doc = None
        self.doc_html = ''
        self.doc_tra_acep = []
        self.doc_tra_html = []
        self.doc_tra = []
        self.doc_tra_acep_str = ''
        self.doc_select_html = []
        self.props['isdoc'] = isdoc
        self.props['tfuente'] = "100%" if isdoc else "115%"
#        if self.session:
#            self.session.record(sentrec, translation=translation)
#        else:
#            print("NO SESSION SO NOTHING TO RECORD")

    def set_props(self, form, bool_props=None, props=None):
        """Set the property values from the form dict. bool-props and props
        are lists of prop strings."""
        if bool_props:
            for prop in bool_props:
                if prop in form:
                    self.props[prop] = form.get(prop) == 'true'
        if props:
            for prop in props:
                if prop in form:
                    self.props[prop] = form[prop]

    def set_domains_texts(self):
        """HTML for a menu listing Text docs available, grouped by domain.
        domain_texts is list of (domain, (id, title)) pairs."""
        domain_texts = get_domains_texts()
        html = "<div class='desplegable-derecha' id='textos'>"
        for dindex, (domain, texts) in enumerate(domain_texts):
            if not texts:
                # no texts for this domain
                html += "<div id='button{}' class='despleg-derecha'>{}</div>".format(dindex, domain)
            else:
                html += "<div onclick=\"desplegarDerecha('despleg{}', 'button{}')\" id='button{}' class='despleg-derecha' style='cursor:context-menu'>{} ▸</div>".format(dindex, dindex, dindex, domain)
                html += "<div id='despleg{}' class='textos-desplegable'>".format(dindex)
                for tindex, (id, title) in enumerate(texts):
                    html += "<div class='opcion' id='opcion{}.{}' onclick='abrirSeleccionado({})'>{}</div>".format(dindex, tindex, id, title)
                html += "</div>"
        html += "</div>"
        self.text_select_html = html
