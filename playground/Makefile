TARGET = paper
CMP    = ../ocamlc
ARG    = -custom unix.cma

all: default run

default:
	@echo "- Compile.."
	@$(CMP) $(ARG) $(TARGET).ml -o $(TARGET)

run:
	@echo "- Run.."
	@./$(TARGET)

clean:
	@rm -f *~ *.cmi *.cmo

white: clean
	@rm -f $(TARGET)
