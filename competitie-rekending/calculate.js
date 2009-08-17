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


    var events = [
        {
            title: '100 meter',
            men:   timeFunction(29550.0, 1881.50),
            women: timeFunction(30672.00, 1682.50)
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
            title: 'Hoogspringen',
            men:   distanceFunction(2440.0, 2593.5),
            women: distanceFunction(2635.6, 2501.5)
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
            var parsedPerformance = parseFloat(performance);

            if (isNaN(parsedEvent) || isNaN(parsedPerformance))
                return -1;

            if (parsedEvent < 0 || parsedEvent >= events.length)
                return -1;

            var event = events[parsedEvent];

            f = (sex) ? event.men : event.women;

            return f(parsedPerformance);

        }

    };


}();
