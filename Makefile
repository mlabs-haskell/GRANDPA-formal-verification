

compile:
	make -C Grandpa

doc:
	make -C Grandpa html
	make -C examples html

examples:
	make -C examples 
