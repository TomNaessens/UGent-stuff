$(function() {
  		$( "#langs" ).accordion({
  			collapsible: true,
  			active: false

  		});
  		$( "#sets" ).accordion({
  			collapsible: true,
  			active: false
  		});
   	$( "#sets li" ).draggable({
     	appendTo: "body",
    	helper: "clone"
    });
    $( "#dropzone" ).droppable({
    	drop: function(event, ui){
    	$( "#" + ui.draggable.attr("class").split(" ")[0]).attr("value",ui.draggable.attr("id"));
    	$( this ).find("." + ui.draggable.attr("class").split(" ")[0]).remove();
    	$( this ).append("<h4 class=" + ui.draggable.attr("class").split(" ")[0] + ">" + ui.draggable.attr("class").split(" ")[0] + "</h4>");
    	$( this ).append("<span class=" + ui.draggable.attr("class").split(" ")[0] + ">" + ui.draggable.attr("id") + "</span>");

    	}
    });

  	});