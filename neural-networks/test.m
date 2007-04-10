% "split-sample" or "hold-out" method

[data, classes] = read_data('irisdata.txt');

targets = [];

% Encode target attributes as vectors of length 3
id = eye(3);
for i = 1:length(classes)
    targets = [targets id(:, classes(i, :))];
end

% For training the net
training_set = [];
training_targets = [];

% For validating different candidates
validation_set = [];
validation_targets = [];

% For measuring the performance of final net
test_set = [];
test_targets = [];

for i = 1:length(data)
    if (mod(i, 3) == 1)
        training_set = [training_set data(:, i)];
        training_targets = [training_targets targets(:, i)];
    elseif (mod(i, 3) == 2)
        validation_set = [validation_set data(:, i)];
        validation_targets = [validation_targets targets(:, i)];
    else
        test_set = [test_set data(:, i)];
        test_targets = [test_targets targets(:, i)];
    end
end

% Create FF Neural Network
% Why minmax over training set?
% Change 'mse' (mean square error) to 'percent_error'

plots = [];

for n = 1:10

    errors = [];

    for i = 1:35

        % Network with i hidden layers
        net = newff(minmax(training_set), [i 3], {'tansig', 'purelin'}, 'traingd', 'learngd', 'mse');
        net = init(net);

        % Don't plot everything you do
        net.trainParam.show = NaN;
        %net.trainParam.epochs = 5;

        % Train the network
        net = train(net, training_set, training_targets);

        % Validate network
        validation_results = sim(net, validation_set);

        errors = [errors percent_error(validation_results - validation_targets)];

    end

    plots = [plots ; errors];

end

for n = 1:10
    plot(1:35, plots(n, :));
    hold on;
end

plot(1:35, mean(plots), 'Color', 'red', 'LineWidth', 2);
