/***********************************************************************

    Competitie rekending

    0.3, 2010-01-27
    Martijn Vermaat <martijn@vermaat.name>
    Sander van der Kruyssen <sandiaan@gmail.com>

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
    Returns NaN in case of invalid parameter values.

    ********************************************************************

    calculator.performance(event, sex, points)

        event:  index
        sex:    boolean
        points: integer

    Returns performance as a formatted string. See the points function
    for parameters event and sex.
    Returns the empty string in case of invalid parameter values.

***********************************************************************/


var calculator = function() {


    function timeEvent(a, b) {

        return {
            points: function(time) {
                var parts = time.split(':');
                var parsedTime = 0.0;
                for (i = 0; i < parts.length; i++)
                    parsedTime += parseFloat(parts[i]) * Math.pow(60, parts.length - i - 1);
                if (isNaN(parsedTime) || parsedTime <= 0)
                    return Number.NaN;
                return Math.max(0, Math.floor(a / parsedTime - b));
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
                var parsedDistance = parseFloat(distance);
                if (isNaN(parsedDistance) || parsedDistance <= 0)
                    return Number.NaN;
                return Math.max(0, Math.floor(a * Math.sqrt(parsedDistance) - b));
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
            title: '3000 meter',
            men:   noEvent,
            women: timeEvent(1197450.00, 1176.00)
        },
        {
            title: '5000 meter',
            men:   timeEvent(1786833.9, 1145.00),
            women: noEvent
        },
        {
            title: '100 meter horden',
            men:   noEvent,
            women: timeEvent(24672.00, 895.50)
        },
        {
            title: '110 meter horden',
            men:   timeEvent(23955.3, 747.90),
            women: noEvent
        },
        {
            title: '400 meter horden',
            men:   timeEvent(96830.9, 912.80),
            women: timeEvent(112752.00, 925.70),
        },
        {
            title: '4*100 meter',
            men:   timeEvent(118175.1, 1880.65),
            women: timeEvent(122328.00, 1677.75)
        },
        {
            title: 'Zweedse estafette',
            men:   timeEvent(247800.0, 1126.00),
            women: timeEvent(261981.50, 865.00)
        },
        {
            title: 'Hoogspringen',
            men:   distanceEvent(2440.0, 2593.5),
            women: distanceEvent(2635.6, 2501.5)
        },
        {
            title: 'Polsstokhoogspringen',
            men:   distanceEvent(1040.0, 1272.5),
            women: noEvent
        },
        {
            title: 'Verspringen',
            men:   distanceEvent(1094.4, 2075.3),
            women: distanceEvent(1076.3, 1729.4)
        },
        {
            title: 'Hinkstapspringen',
            men:   distanceEvent(762.9, 2074.5),
            women: distanceEvent(750.3, 1730.6)
        },
        {
            title: 'Kogelstoten',
            men:   distanceEvent(462.5, 1001.8),
            women: distanceEvent(429.5, 768.3)
        },
        {
            title: 'Discuswerpen',
            men:   distanceEvent(249.8, 893.5),
            women: distanceEvent(224.8, 686.5)
        },
        {
            title: 'Speerwerpen',
            men:   distanceEvent(190.2, 711.3),
            women: distanceEvent(197.5, 482.5)
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

            if (isNaN(parsedEvent))
                return Number.NaN;

            if (parsedEvent < 0 || parsedEvent >= events.length)
                return Number.NaN;

            f = (sex) ? events[parsedEvent].men : events[parsedEvent].women;

            return f.points(performance);

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

        }


    };


}();
