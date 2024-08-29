from abc import ABC, abstractmethod
from transition import TransitionSystem

class Program(ABC):

    @abstractmethod
    def get_transition_system(self) -> TransitionSystem:
        pass
    
    @abstractmethod
    def get_trivial_g(self) -> float:
        pass
