test:
	agda Everything.agda
# For me:
# agda -i /home/patrikj/lib/agda-stdlib/ -i . Everything.agda

abstract:
	make -C doc/
