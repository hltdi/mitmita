#
#   Mainumby Database helper functions.
#   Uses the Object Relational Mapper implementation of SQLAlchemy.
#
########################################################################
#
#   This file is part of the PloGs project
#   for parsing, generation, translation, and computer-assisted
#   human translation.
#
#   Copyright (C) 2015, 2016, 2019 PLoGS <gasser@indiana.edu>
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

# 2019.08.19
# -- Created (but not used for anything)

from .text import *

class TextDB:
    """Container for text database functions."""

    @staticmethod
    def align(translation):
        """
        Given a Translation object from the Text DB, align its TraSegs
        with the corresponding TextSegs in the corresponding Text object,
        return a list of pairs of strings.
        """
        text = translation.text
        textsegs = text.segments
        text_trans = []
        for traseg in translation.trasegs:
            traindex = traseg.index
            textseg = textsegs[traindex]
            if textseg.index != traindex:
                print("Warning: index mismatch: text {}, tra {}".format(textseg.index, traindex))
            else:
                text_trans.append((textseg.content, traseg.content))
        return text_trans

### Various utility functions for DB classes

def db_serialize_class(klass):
    """Return a list of dicts, one for each member of DB class."""
    return [obj.to_dict() for obj in db_list(klass)]

#def db_recreate_session():
#    kuaa.db.session = kuaa.db.create_scoped_session()

#def db_create(db=None):
#    """db puede ser también 'text' o 'lex'."""
#    kuaa.db.create_all(bind=db)

#def db_destroy(db=None):
#    """db puede ser también 'text' o 'lex'."""
#    kuaa.db.drop_all(bind=db)

def db_list(klass):
    """klass is something like kuaa.Text."""
    return db.session.query(klass).all()

def db_add(instance):
    db.session.add(instance)

def db_delete(instance):
    db.session.delete(instance)
