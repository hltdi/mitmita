/*! SaveDoc.js demo script
 *  2016-05-15
 *
 *  Based on FileSaver demo
 *  By Eli Grey, http://eligrey.com
 *  2012-01-23
 *  License: X11/MIT
 */

(function(view) {
"use strict";

var
	  document = view.document
	, $ = function(id) {
		return document.getElementById(id);
	}
	, session = view.sessionStorage
	// only get URL when necessary in case Blob.js hasn't defined it yet
	, get_blob = function() {
		return view.Blob;
	}

	, text = $("document")
	, text_options_form = $("text-options")
	, text_filename = $("text-filename")
;
  if (session.text) {
	text.value = session.text;
} if (session.text_filename) {
	text_filename.value = session.text_filename;
}

text_options_form.addEventListener("submit", function(event) {
	event.preventDefault();
	var BB = get_blob();
	saveAs(
		  new BB(
			  [text.value || text.placeholder]
			, {type: "text/plain;charset=" + document.characterSet}
		)
		, (text_filename.value || text_filename.placeholder)
	);
}, false);

view.addEventListener("unload", function() {

	session.text = text.value;
	session.text_filename = text_filename.value;

}, false);
}(self));
