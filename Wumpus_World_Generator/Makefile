all:
	@-rm -rf Worlds
	@-mkdir Worlds
	@echo ""
	@read -p "Enter Row Dimension: " rDim; \
	 echo ""; \
	 read -p "Enter Column Dimension: " cDim; \
	 echo ""; \
	 read -p "How many worlds created?: " count; \
	 echo ""; \
	 python3 world_generator.py Worlds/world $${count} $${rDim} $${cDim}

tournamentSet:
	@-rm -rf Worlds
	@-mkdir Worlds
	@python3 world_generator.py Worlds/world4x4 10 4 4
	@python3 world_generator.py Worlds/world4x5 10 4 5
	@python3 world_generator.py Worlds/world4x6 10 4 6
	@python3 world_generator.py Worlds/world4x7 10 4 7
	@python3 world_generator.py Worlds/world5x4 10 5 4
	@python3 world_generator.py Worlds/world5x5 10 5 5
	@python3 world_generator.py Worlds/world5x6 10 5 6
	@python3 world_generator.py Worlds/world5x7 10 5 7
	@python3 world_generator.py Worlds/world6x4 10 6 4
	@python3 world_generator.py Worlds/world6x5 10 6 5
	@python3 world_generator.py Worlds/world6x6 10 6 6
	@python3 world_generator.py Worlds/world6x7 10 6 7
	@python3 world_generator.py Worlds/world7x4 10 7 4
	@python3 world_generator.py Worlds/world7x5 10 7 5
	@python3 world_generator.py Worlds/world7x6 10 7 6
	@python3 world_generator.py Worlds/world7x7 10 7 7
