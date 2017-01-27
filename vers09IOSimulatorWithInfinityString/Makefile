agdafiles= $(wildcard *.agda)
agdaifiles= $(agdafiles:%.agda=%.agdai) 


%.agdai : %.agda
	agda -i. -i$(agda_stdlib) --allow-unsolved-meta $<

default: $(agdaifiles)


test:
	echo agdafiles = 
	echo $(agdafiles)
	echo agdaifiles = 
	echo $(agdaifiles)
