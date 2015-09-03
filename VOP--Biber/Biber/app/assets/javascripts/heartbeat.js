 //Setting the timer to notify the server each ONLINEINTERVALMIN minutes
var ONLINEINTERVALMIN = 1;
$(document).ready(function() {
    jsRoutes.controllers.ProfilesController.renewOnline().ajax({
        async: true
    });
});

setInterval(function() {
    jsRoutes.controllers.ProfilesController.renewOnline().ajax({
        async: true
    });
}, 1000 * 60 * ONLINEINTERVALMIN);
/*
//Before closing the page, notifying the server that the user has left
$(window).on('beforeunload ',function() {
    jsRoutes.controllers.ProfilesController.logout().ajax({
        async: false
    });
});
*/