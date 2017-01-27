agdafiles= $(wildcard *.agda) $(wildcard ooAgda/*.agda)\
           $(wildcard ooAgda/SizedIO/*.agda) 
agdaifiles= $(agdafiles:%.agda=%.agdai) 


%.agdai : %.agda
	agda -i. -i$(agda_stdlib) --allow-unsolved-meta $<

default: $(agdaifiles)

html: 
	agda -i. -i$(agda_stdlib) --allow-unsolved-meta --html loadAllForTesting.agda


clean :
	rm -f $(agdaifiles)
	rm -r html       

test:
	echo agdafiles = 
	echo $(agdafiles)
	echo agdaifiles = 
	echo $(agdaifiles)
