# Mit'mit'a. Lexical DB.
#
########################################################################
#
#   This file is part of the Mainumby project within the PLoGS metaproject
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
# 2019.8.18
# -- Created

from . import db

class Lex(db.Model):
    """A lexical entry."""

    __tablename__ = 'lexes'
    __bind_key__ = "lex"

    id = db.Column(db.Integer, primary_key=True)
    tokens = db.Column(db.String)

    def __init__(self, tokens):
        self.tokens = tokens

    def __repr__(self):
        return "<Lex({}, {})>".format(self.id, self.tokens)
