/* Loading morphology data */
function cargando() {
    document.getElementById("cargando").innerHTML = "<p></p><span class='cargando'>መዝገበ ቃላትና ሰዋሰው እያስበጋ ነው...</span><p></p>";
}
/* When the user clicks on the button, toggle between hiding and showing the dropdown content */
function mostrarDespleg() {
    menu = document.getElementById("menudespleg");
    list = menu.classList;
    list.toggle("show");
}
function error(msg) {
    document.getElementById("error").innerHTML = msg;
}

function borrarError(msg) {
    document.getElementById("error").innerHTML = "";
}

// Close the dropdown if the user clicks outside of it
window.onclick = function(event) {
    if (!event.target.matches('.despleg')) {
	var dropdowns = document.getElementsByClassName("contenido-desplegable");
	var i;
	for (i = 0; i < dropdowns.length; i++) {
	    var openDropdown = dropdowns[i];
	    if (openDropdown.classList.contains('show')) {
		openDropdown.classList.remove('show');
	    }
	}
	dropdowns = document.getElementsByClassName("contenido-despleg");
	for (i = 0; i < dropdowns.length; i++) {
	    var openDropdown = dropdowns[i];
	    if (openDropdown.classList.contains('show')) {
		openDropdown.classList.remove('show');
	    }
	}
    }
}
