function w = perceptron(X,d)

[m N] = size(X);
X=[ones(1,N);X];
lr=1; %learning rate
w=rand(m+1,1);%initialisation
nr_iter=0;
while 1
    misclass = 0; %look for misclassified example
     nr_iter=nr_iter+1;
    i=1;
    I=randperm(N);
    while i<=N
        y=sign(w'*X(:,I(i)));%Computation of actual response
       
        if y ~= d(1,I(i))
            misclass=1;
            w=w+lr*(d(1,I(i))-y)*X(:,I(i));%Adaptation of weight vector
        end
        i=i+1;
    end
    if misclass ==0
        break;
    end
end %while 1

if m==2
    lpos=find(d'>0);
    plot(X(2,lpos),X(3,lpos),'b.');%+1 class, blue
    
    axis([0 1 0 1]);
    hold on;
    
    lneg=find(d'<0);
    plot(X(2,lneg),X(3,lneg),'r.'); % -1 class, red
    
    x1=0:1;
    x2=-(w(2)*x1+w(1))/w(3);% the decision boundary
    plot(x1,x2,'k-');
    
    hold off;
    pause(0.2)
    
end

lneg = find(d<0);
X(:,lneg)=-1*X(:,lneg);

alpha = min(w'*X);

norms = zeros(1,N);

for i = 1:N
    norms(1,i)=norm(X(:,i),2)^2;
end

beta=max(norms);
fprintf(1,'Actual nr iter= %d. Theoretical upperbound=%f\n', nr_iter, (norm(w,2)^2*beta)/(alpha^2));