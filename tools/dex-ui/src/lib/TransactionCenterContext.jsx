const transactionCenter = {
  transactions: [],
  pendingCount: 0,
  upsertTransaction: () => null,
  removeTransaction: () => {},
  clearSettled: () => {},
};

export function useTransactionCenter() {
  return transactionCenter;
}
