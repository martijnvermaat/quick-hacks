function pe = percent_error(errors, Y, X, FP)
% Percent error performance function

% Closest integer value counts
errors = round(errors);

num_errors = 0;

for i = 1:length(errors)
    if max(errors(:, i)) > 0
        num_errors = num_errors + 1;
    end
end

pe = 100 * num_errors / length(errors);
