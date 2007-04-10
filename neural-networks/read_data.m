function [data, classes] = read_data(file)
% Read Iris dataset from file to data matrix

% Read data attributes and classname
[a,b,c,d,n] = textread(file, '%f,%f,%f,%f,%s');

% Get corresponding integers for classnames
for i = 1:length(n)
    ints(i) = class_to_int(n{i});
end

data = [a b c d ints'];

% Sort data ascending according to class
data = sortrows(data, [5]);

% Save last column
classes = data(:, 5);

% Delete last column
data = data(:, 1:4);

% Print some statistics
fprintf('Maximal values: %s\n', mat2str(max(data)));
fprintf('Minimal values: %s\n', mat2str(min(data)));
fprintf('Mean values: %s\n', mat2str(mean(data)));
fprintf('Std deviation: %s\n', mat2str(std(data)));

% Transpose data
data = data';
