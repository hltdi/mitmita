#!/bin/bash

virtualenv -p /usr/bin/python3 venv
. venv/bin/activate
pip3 install Flask
#pip install sqlalchemy
#pip install beautifulsoup4
#pip install python-social-auth
#pip install requests

#pip install pyyaml
#pip install https://github.com/nltk/nltk/tarball/develop
## make sure we have sentence segmenter models
#python3 -m nltk.downloader punkt
