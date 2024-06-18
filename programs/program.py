from abc import ABC, abstractmethod

class Program(ABC):

    @abstractmethod
    def get_transition_system(self):
        pass
