/***********************************************************************

    Competitie rekending

    0.2, 2009-08-18
    Martijn Vermaat, martijn@vermaat.name

    Given a time or distance performed at a competition event, calculate
    the number of points. And the other way around.

    Formulas are taken from 'Formules en Constanten' [1], January 2004
    version, part of Wedstrijdreglement Atletiekunie.

    [1] http://www.atletiekunie.nl/upload/File/Dutch_Athletes/Formules%20en%20constanten%20(20-11-03).doc

***********************************************************************/


/***********************************************************************

    Available functions

    ********************************************************************

    calculator.events()

    Returns an array of event titles. The array indices can be used as
    the first parameter to the calculate function.

    ********************************************************************

    calculator.points(event, sex, performance)

        event:       index
        sex:         boolean
        performance: distance or time

    Returns number of points as integer. The value true for parameter
    sex indicates a male athlete, false a female athlete. The
    performance parameter is either a distance in meters as float, or a
    time in seconds as float. A time in seconds is optionally preceeded
    by a time in minutes as float and a : character.

    ********************************************************************

    calculator.performance(event, sex, points)

        event:  index
        sex:    boolean
        points: integer

    Returns performance as a formatted string. See the points function
    for parameters event and sex.

***********************************************************************/


var calculator = function() {


    function timeEvent(a, b) {

        return {
            points: function(time) {
                return Math.max(0, Math.floor(a / time - b));
            },
            performance: function(points) {
                var performance;
                var seconds = a / (points + b);
                if (seconds <= 0.0)
                    return '';
                if (seconds >= 60.0) {
                    minutes = Math.floor(seconds / 60);
                    seconds = (seconds % 60).toFixed(2);
                    if (seconds >= 10.0)
                        performance = minutes + ':' + seconds;
                    else
                        performance = minutes + ':0' + seconds;
                } else {
                    performance = seconds.toFixed(2).toString();
                }
                return performance;
            }
        };

    };


    function distanceEvent(a, b) {

        return {
            points: function(distance) {
                return Math.max(0, Math.floor(a * Math.sqrt(distance) - b));
            },
            performance: function(points) {
                return Math.pow((points + b) / a, 2).toFixed(2).toString();
            }
        };

    };


    var noEvent = {
        points: function(performance) {
            return Number.NaN;
        },
        performance: function(points) {
            return '';
        }
    };


    var events = [
        {
            title: '100 meter',
            men:   timeEvent(29550.0, 1881.50),
            women: timeEvent(30672.00, 1682.50)
        },
        {
            title: '200 meter',
            men:   timeEvent(52611.4, 1547.10),
            women: timeEvent(54720.00, 1342.00)
        },
        {
            title: '400 meter',
            men:   timeEvent(111960.0, 1433.50),
            women: timeEvent(111720.00, 1084.50)
        },
        {
            title: '800 meter',
            men:   timeEvent(248544.0, 1323.20),
            women: timeEvent(247200.00, 975.50)
        },
        {
            title: '1500 meter',
            men:   timeEvent(489971.4, 1224.70),
            women: timeEvent(557448.00, 1181.50)
        },
        {
            title: '5000 meter',
            men:   timeEvent(1786833.9, 1145.00),
            women: noEvent
        },
        {
            title: 'Hoogspringen',
            men:   distanceEvent(2440.0, 2593.5),
            women: distanceEvent(2635.6, 2501.5)
        },
        {
            title: 'Verspringen',
            men:   distanceEvent(1094.4, 2075.3),
            women: distanceEvent(1076.3, 1729.4)
        },
        {
            title: 'Discuswerpen',
            men:   distanceEvent(249.8, 893.5),
            women: distanceEvent(224.8, 686.5)
        }
    ];


    return {


        events: function() {

            var titles = [];
            for (i = 0; i < events.length; i++)
                titles.push(events[i].title);
            return titles;

        },


        points: function(event, sex, performance) {

            var f;
            var parsedEvent = parseInt(event);
            var parts = performance.split(':');
            var parsedPerformance = 0;

            for (i = 0; i < parts.length; i++)
                parsedPerformance += parseFloat(parts[i]) * Math.pow(60, parts.length - i - 1);

            if (isNaN(parsedEvent) || isNaN(parsedPerformance))
                return Number.NaN;

            if (parsedPerformance <= 0)
                return Number.NaN;

            if (parsedEvent < 0 || parsedEvent >= events.length)
                return Number.NaN;

            f = (sex) ? events[parsedEvent].men : events[parsedEvent].women;

            return f.points(parsedPerformance);

        },


        performance: function(event, sex, points) {

            var f;
            var parsedEvent = parseInt(event);
            var parsedPoints = parseInt(points);

            if (isNaN(parsedEvent) || isNaN(parsedPoints))
                return '';

            if (parsedPoints < 0)
                return '';

            if (parsedEvent < 0 || parsedEvent >= events.length)
                return '';

            f = (sex) ? events[parsedEvent].men : events[parsedEvent].women;

            return f.performance(parsedPoints);

        },


    };


}();
