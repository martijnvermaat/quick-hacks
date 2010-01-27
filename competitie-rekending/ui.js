$(document).ready(function() {


    var TO_POINTS = 0;
    var TO_PERFORMANCE = 1;

    var direction = TO_POINTS;
    var sum = 0;


    var calculate = function() {

        if (direction == TO_POINTS) {
            var points = calculator.points($('#events').val(),
                                           $('#male').is(':checked'),
                                           $('#performance').val());
            if (!isNaN(points))
                $('#points').val(points.toString());
        } else {
            $('#performance').val(
                calculator.performance($('#events').val(),
                                       $('#male').is(':checked'),
                                       $('#points').val()));
        }

        if (isNaN(parseInt($('#events').val()))
            || $('#points').val() == ''
            || $('#performance').val() == '')
            $('#bookmark').hide();
        else
            $('#bookmark').show();

    };


    var to_points = function() {
        direction = TO_POINTS;
        calculate();
    };


    var to_performance = function() {
        direction = TO_PERFORMANCE;
        calculate();
    };


    var bookmark = function() {

        var r = $('<a href="#" class="remove">Verwijder dit resultaat</a>');
        r.attr('title', r.text()).click(function() {
            $(this).parent().remove();
            updateSum(-parseInt($('#points').val())); // TODO: this doesn't use current value of points
            return false;
        });

        var sex = $('#male').is(':checked') ? 'm' : 'v';
        var s = $('#events option:selected').text() + ' (' + sex + '): ' + $('#performance').val() + ', ' + $('#points').val();

        $('#bookmarks').append(
            $('<li>').text(s).prepend(r)
        );

        updateSum(parseInt($('#points').val()));

    };


    var updateSum = function(points) {

        sum += points;
        var count = $('#bookmarks li').length;

        if (count > 1) {
            $('#sum').text(count + ' resultaten met een totaal van ' + sum + ' punten.').show();
        } else {
            $('#sum').hide();
        }

    }


    var events = calculator.events();
    for (i = 0; i < events.length; i++)
        $('#events').append($('<option>').val(i).text(events[i]));

    $('#events').bind('change keyup', calculate);

    $('#male, #female').click(calculate);

    $('#performance').keyup(to_points);
    $('#points').keyup(to_performance);

    $('#bookmark').click(function() { bookmark(); return false; }).hide();

    $('#sum').hide();


});
