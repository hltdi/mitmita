/* Loading morphology data */
function cargando() {
    document.getElementById("cargando").innerHTML = "<p></p><span class='cargando'>መዝገበ ቃላትና ሰዋሰው እያስገባ ነው...</span><p></p>";
}
/* When the user clicks on the button, toggle between hiding and showing the dropdown content */
// function mostrarDespleg() {
//     menu = document.getElementById("menudespleg");
//     list = menu.classList;
//     list.toggle("show");
// }
function error(msg) {
    document.getElementById("error").innerHTML = msg;
}

function eraseError(msg) {
    document.getElementById("error").innerHTML = "";
}
