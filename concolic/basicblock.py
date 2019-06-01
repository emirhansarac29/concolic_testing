class BasicBlock:
    def __init__(self, start_pc, end_pc, termination_status, targets):
        self.start = start_pc
        self.end = end_pc
        self.opcodes = []
        self.targets = targets
        self.termination = termination_status
