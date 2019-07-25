## Growing List , used as memory in simulation
class GrowingList(list):
    def __setitem__(self, index, value):
        if index >= len(self):
            self.extend(["00"]*(index + 1 - len(self)))
        list.__setitem__(self, index, value)