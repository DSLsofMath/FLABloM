test:
	agda Everything.agda # Agda 2.5.1 (with standard-library set up)
# For me:
# agda -i /home/patrikj/lib/agda-stdlib/ -i . Everything.agda

abstract:
	make -C doc/
