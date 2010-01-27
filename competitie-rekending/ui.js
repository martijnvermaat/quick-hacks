$(document).ready(function() {


    var TO_POINTS = 0;
    var TO_PERFORMANCE = 1;
    var direction = TO_POINTS;


    var calculate = function() {

        if (direction == TO_POINTS) {
            var points = calculator.points($('#events').val(),
                                             $('#male').is(':checked'),
                                             $('#performance').val());
            if (!isNaN(points))
                $('#points').val(points.toString());
        } else {
            $('#performance').val(calculator.performance(
                $('#events').val(),
                $('#male').is(':checked'),
                $('#points').val()));
        }

    };


    var to_points = function() {
        direction = TO_POINTS;
        calculate();
    };


    var to_performance = function() {
        direction = TO_PERFORMANCE;
        calculate();
    };


    var events = calculator.events();
    for (i = 0; i < events.length; i++)
        $('#events').append($('<option>').val(i).text(events[i]));

    $('#events').bind('change keyup', calculate);

    $('#male, #female').click(calculate);

    $('#performance').keyup(to_points);
    $('#points').keyup(to_performance);


});
