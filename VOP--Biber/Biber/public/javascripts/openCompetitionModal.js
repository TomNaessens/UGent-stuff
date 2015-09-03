$(function() {
    $('.openCompButton').click(function(e) {
        var id = $('#val'+$(this).attr('id')).val();
        jsRoutes.controllers.Competitions.openCompetition(id).ajax().done(
    			function(result){
    				if (result == null) return;
    				if (result.forbidden) {
    				$('#openerror'+id).text("Snap, something wrong happened");
    				} else {
  						$('#opensucces'+id).css("display","inline");
  						$('#close'+id).css("display","none");
  						$('#opencomptext'+id).text("The competition has been opened");
    				}
    			});
    });
});
