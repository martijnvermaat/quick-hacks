function [X,t] = make_data_perc(N)

t=zeros(1,N); %Class labels
X = rand(2,N);
X(1,:)=X(1,:)*0.9;

for i=1:N
    if X(1,i)>X(2,i)
        t(1,i)=-1;
        X(1,i)=X(1,i)+0.1;
    else
        t(1,i)=1;
    end
end

