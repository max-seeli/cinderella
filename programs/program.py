from abc import ABC, abstractmethod
from transition import TransitionSystem

class Program(ABC):

    @abstractmethod
    def get_transition_system(self) -> TransitionSystem:
        pass
