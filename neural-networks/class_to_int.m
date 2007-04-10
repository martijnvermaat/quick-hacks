function intclass = class_to_int(classname)
% Integer representation of given classname

if (strcmp(classname, 'Iris-virginica'))
    intclass = 3;
elseif (strcmp(classname, 'Iris-versicolor'))
    intclass = 2;
elseif (strcmp(classname, 'Iris-setosa'))
    intclass = 1;
else 
    intclass = 0;
    fprintf('[error] Class not recognized: %s', classname);
end
