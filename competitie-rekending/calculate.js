/***********************************************************************

    Competitie rekending

    0.1, 2009-08-17
    Martijn Vermaat, martijn@vermaat.name

    Given a time or distance performed at a competition event, calculate
    the number of points.

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

    calculator.calculate(event, sex, performance)

        event:       index
        sex:         boolean
        performance: distance or time

    Returns number of points as integer. The value true for  parameter
    sex indicates a male athlete, false a female athlete. The
    performance parameter is either a distance in meters as float, or a
    time in seconds as float. A time in seconds is optionally preceeded
    by a time in minutes as float and a : character.

***********************************************************************/


var calculator = function() {


    function timeFunction(a, b) {

        return function(time) {
            return Math.floor(a / time - b);
        };

    };


    function distanceFunction(a, b) {

        return function(distance) {
            return Math.floor(a * Math.sqrt(distance) - b);
        };

    };


    var noFunction = function(performance) {
        return Number.NaN;
    }


    var events = [
        {
            title: '100 meter',
            men:   timeFunction(29550.0, 1881.50),
            women: timeFunction(30672.00, 1682.50)
        },
        {
            title: '200 meter',
            men:   timeFunction(52611.4, 1547.10),
            women: timeFunction(54720.00, 1342.00)
        },
        {
            title: '400 meter',
            men:   timeFunction(111960.0, 1433.50),
            women: timeFunction(111720.00, 1084.50)
        },
        {
            title: '800 meter',
            men:   timeFunction(248544.0, 1323.20),
            women: timeFunction(247200.00, 975.50)
        },
        {
            title: '1500 meter',
            men:   timeFunction(489971.4, 1224.70),
            women: timeFunction(557448.00, 1181.50)
        },
        {
            title: '5000 meter',
            men:   timeFunction(1786833.9, 1145.00),
            women: noFunction
        },
        {
            title: 'Hoogspringen',
            men:   distanceFunction(2440.0, 2593.5),
            women: distanceFunction(2635.6, 2501.5)
        },
        {
            title: 'Verspringen',
            men:   distanceFunction(1094.4, 2075.3),
            women: distanceFunction(1076.3, 1729.4)
        },
        {
            title: 'Discuswerpen',
            men:   distanceFunction(249.8, 893.5),
            women: distanceFunction(224.8, 686.5)
        }
    ];


    return {


        events: function() {

            var titles = [];
            for (i = 0; i < events.length; i++)
                titles.push(events[i].title);
            return titles;

        },


        calculate: function(event, sex, performance) {

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

            var event = events[parsedEvent];

            f = (sex) ? event.men : event.women;

            return Math.max(0, f(parsedPerformance));

        }

    };


}();
